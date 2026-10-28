"""
serve_playlist.py
 
Runs a small web server on your PC. Every REFRESH_MINUTES it reads your
website's schedule page, extracts the events with a tiered parser, and keeps
the resulting M3U playlist in memory. IPTV apps always get the latest saved
playlist instantly. If a refresh fails, the last good playlist keeps being served.
 
Crawling: starting at PAGE_URL it also follows links that stay on the same domain
(for example category pages, then event pages) and collects events from all of them.
The text of the link that led to a page is used as the category when none is found.
 
Parsing strategies on each page (tried in order, first one that finds events wins):
  1. TABLE  - any <table>; columns detected from header names, with the
              COL_* positions below as fallback.
  2. CARDS  - repeating containers (.event-item, .art-card, div[class*="card"], ...)
  3. LINKS  - heuristic scan of the whole page for media URLs (.m3u8, .mpd, .mp4 ...)
              in links, <video>/<source> tags, data-* attributes and embedded scripts/JSON.
 
Install:  pip install requests beautifulsoup4
Run:      python serve_playlist.py
Test a saved page without the server:
          python serve_playlist.py --file page.html
Build once and save to a file (GitHub Actions):
          python serve_playlist.py --out playlist.m3u
"""
 
import argparse
import html as html_lib
import re
import sys
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import urljoin, urlparse
 
import requests
from bs4 import BeautifulSoup
 
# ---------------------------------------------------------------------------
# CONFIGURATION: edit these
# ---------------------------------------------------------------------------
PAGE_URL = "https://vipbox.fm/home"
PORT = 8000
REFRESH_MINUTES = 15
REQUEST_TIMEOUT = 15
USER_AGENT = "Mozilla/5.0 (compatible; PortfolioPlaylistBuilder/2.0)"
 
# Forgive a missing scheme, e.g. "example.com/home" -> "https://example.com/home"
if not PAGE_URL.startswith(("http://", "https://")):
    PAGE_URL = "https://" + PAGE_URL
 
DEFAULT_CATEGORY = "Events"      # used when no category can be found
 
# --- Site crawling (follows links on your own domain: categories -> events) ---
CRAWL = True                     # False = read only PAGE_URL
CRAWL_MAX_PAGES = 60             # safety limit per refresh
CRAWL_MAX_DEPTH = 2              # 0 = start page only, 1 = + linked pages, 2 = + their links
CRAWL_DELAY = 0.3                # seconds between page requests (be gentle on your site)
SKIP_LINK_RE = re.compile(
    r"\.(jpg|jpeg|png|gif|webp|svg|ico|css|js|json|xml|pdf|zip|woff2?|ttf|mp3)(?:[?#]|$)", re.I)
 
# --- Strategy 1: tables ---
TABLE_SELECTOR = "table"
ROW_SELECTOR = "tr"
# Fallback column positions (zero-based) if headers can't be recognised
COL_TITLE = 0
COL_CATEGORY = 1
COL_URL = 2
# Words that identify columns by their header text (lowercase)
COLUMN_KEYWORDS = {
    "title":    ("title", "name", "event", "film", "show", "program", "programme"),
    "category": ("category", "type", "genre", "group", "section"),
    "url":      ("url", "stream", "link", "video", "watch", "source"),
}
 
# --- Strategy 2: card / grid containers (tried in this order) ---
CARD_SELECTORS = [
    ".event-item", ".event-card", ".event", ".art-card", ".film-card",
    ".video-card", ".video-item", ".stream-item", ".schedule-item",
    ".program-item", ".grid-item", ".card", "article",
    "li[class*='event']", "li[class*='item']",
    "div[class*='event']", "div[class*='card']", "div[class*='item']",
]
# If True, a card with no recognisable media link may use its first plain link.
ALLOW_ANY_LINK_IN_CARDS = False
 
# --- What counts as a media/stream URL ---
MEDIA_RE = re.compile(r"\.(m3u8|m3u|mpd|mp4|m4v|webm|mkv|mov|ts|flv)(?:[?#]|$)", re.I)
STREAM_SCHEMES = ("rtmp://", "rtsp://", "srt://")
# Extra path hints, only used in strategies 1 and 2 (not the heuristic scan)
LOOSE_MEDIA_HINTS = ("/live/", "/hls/", "/stream/", "/streams/")
# ---------------------------------------------------------------------------
 
URL_ATTRS = ("href", "src", "data-src", "data-url", "data-stream",
             "data-video", "data-href", "data-hls", "data-file")
GENERIC_LABELS = {"watch", "play", "stream", "link", "click here", "here", "live",
                  "open", "download", "watch now", "play now", "view", "more", "▶"}
RAW_URL_RE = re.compile(r"""(?:https?|rtmp|rtsp|srt)://[^\s"'<>\\)]+""", re.I)
 
_lock = threading.Lock()
_playlist = "#EXTM3U\n"
_last_strategy = None
 
 
# ----------------------------- helpers -------------------------------------
 
def clean(text):
    return " ".join((text or "").split()).replace('"', "'")
 
 
def clean_category(text):
    return clean(text).replace(",", " ")[:40].strip()
 
 
def text_of(el):
    return clean(el.get_text(" ")) if el is not None else ""
 
 
def is_media_url(url, loose=False):
    low = url.lower()
    if low.startswith(STREAM_SCHEMES) or MEDIA_RE.search(low):
        return True
    return loose and any(h in low for h in LOOSE_MEDIA_HINTS)
 
 
def normalize_url(raw, base):
    raw = html_lib.unescape((raw or "").strip())
    if not raw or raw.startswith(("#", "javascript:", "mailto:", "tel:", "data:")):
        return None
    url = urljoin(base, raw)
    if urlparse(url).scheme not in ("http", "https", "rtmp", "rtsp", "srt"):
        return None
    return url
 
 
def name_from_url(url):
    path = urlparse(url).path.rstrip("/")
    stem = path.rsplit("/", 1)[-1] or urlparse(url).netloc
    stem = re.sub(r"\.[A-Za-z0-9]{2,5}$", "", stem)
    return clean(re.sub(r"[-_]+", " ", stem)).title() or url
 
 
def candidate_urls(node, base):
    """All URLs found in a node's own and descendants' link-like attributes."""
    urls = []
    for el in [node] + node.find_all(True):
        for attr in URL_ATTRS:
            val = el.get(attr)
            if isinstance(val, str):
                u = normalize_url(val, base)
                if u and u not in urls:
                    urls.append(u)
    return urls
 
 
def pick_url(node, base, allow_any=False, loose=True):
    """Best stream URL inside a node: a media URL, else (optionally) the first plain link."""
    cands = candidate_urls(node, base)
    for u in cands:
        if is_media_url(u, loose=loose):
            return u
    if allow_any:
        a = node if node.name == "a" and node.get("href") else node.find("a", href=True)
        if a is not None:
            return normalize_url(a.get("href"), base)
        txt = text_of(node)
        if txt.lower().startswith(("http://", "https://", "rtmp://", "rtsp://", "srt://")):
            return normalize_url(txt, base)
    return None
 
 
def dedupe(events):
    seen, out = set(), []
    for ev in events:
        if ev["url"] not in seen:
            seen.add(ev["url"])
            out.append(ev)
    return out
 
 
def make_event(title, category, url):
    return {
        "title": clean(title) or name_from_url(url),
        "category": clean_category(category) or DEFAULT_CATEGORY,
        "url": url,
    }
 
 
# -------------------- Strategy 1: tables -----------------------------------
 
def guess_columns(table):
    """Map title/category/url to column indexes using the header row text."""
    header = None
    for row in table.select(ROW_SELECTOR):
        if row.find("th"):
            header = row
            break
    if header is None:
        return {}
    names = [text_of(c).lower() for c in header.find_all(["th", "td"])]
    mapping, used = {}, set()
    for field in ("title", "category", "url"):
        for i, name in enumerate(names):
            if i not in used and any(w in name for w in COLUMN_KEYWORDS[field]):
                mapping[field] = i
                used.add(i)
                break
    return mapping
 
 
def parse_tables(soup, raw_html, base):
    events = []
    for table in soup.select(TABLE_SELECTOR):
        cols = guess_columns(table)
        ti = cols.get("title", COL_TITLE)
        ci = cols.get("category", COL_CATEGORY)
        ui = cols.get("url", COL_URL)
        for row in table.select(ROW_SELECTOR):
            cells = row.find_all("td")
            if not cells:
                continue
            title = text_of(cells[ti]) if ti < len(cells) else ""
            category = text_of(cells[ci]) if ci < len(cells) else ""
            url = pick_url(cells[ui], base, allow_any=True) if ui < len(cells) else None
            if not url:
                url = pick_url(row, base)          # any media link elsewhere in the row
            if url:
                events.append(make_event(title, category, url))
    return dedupe(events), "table"
 
 
# -------------------- Strategy 2: cards ------------------------------------
 
def find_title(node):
    for sel in ("h1", "h2", "h3", "h4", "h5", "[itemprop=name]",
                "[class*=title]", "[class*=name]"):
        t = text_of(node.select_one(sel))
        if t:
            return t
    img = node.find("img", alt=True)
    if img and clean(img["alt"]):
        return clean(img["alt"])
    for el in [node] + node.find_all("a"):
        for attr in ("title", "aria-label"):
            if clean(el.get(attr, "")):
                return clean(el[attr])
    for a in node.find_all("a"):
        t = text_of(a)
        if t and t.lower() not in GENERIC_LABELS:
            return t
    return ""
 
 
def find_category(node):
    for attr in ("data-category", "data-type", "data-genre"):
        if node.get(attr):
            return node[attr]
    el = node.select_one("[class*=category],[class*=genre],[class*=tag],"
                         "[class*=badge],[class*=type],[class*=label]")
    return text_of(el) if el is not None else ""
 
 
def parse_cards(soup, raw_html, base):
    for sel in CARD_SELECTORS:
        try:
            nodes = soup.select(sel)
        except Exception:
            continue
        events = []
        for node in nodes:
            url = pick_url(node, base, allow_any=ALLOW_ANY_LINK_IN_CARDS)
            if url:
                events.append(make_event(find_title(node), find_category(node), url))
        events = dedupe(events)
        if events:
            return events, f"cards ({sel})"
    return [], "cards"
 
 
# -------------------- Strategy 3: heuristic scan ---------------------------
 
def title_near(el, url):
    for attr in ("title", "aria-label"):
        if clean(el.get(attr, "")):
            return clean(el[attr])
    t = text_of(el)
    if t and t.lower() not in GENERIC_LABELS and len(t) <= 100:
        return t
    node = el
    for _ in range(3):                      # look at the surrounding block
        node = node.parent
        if node is None or node.name in ("body", "html", "[document]"):
            break
        t = find_title(node)
        if t:
            return t
    return name_from_url(url)
 
 
def heading_before(el):
    h = el.find_previous(["h2", "h3"])
    t = text_of(h)
    return t if t and len(t) <= 40 else ""
 
 
def parse_links(soup, raw_html, base):
    events, seen = [], set()
    # a) structured elements carrying a media URL
    for el in soup.find_all(True):
        for attr in URL_ATTRS:
            val = el.get(attr)
            if not isinstance(val, str):
                continue
            url = normalize_url(val, base)
            if url and is_media_url(url) and url not in seen:
                seen.add(url)
                events.append(make_event(title_near(el, url), heading_before(el), url))
    # b) media URLs sitting in scripts / JSON / plain text
    text = html_lib.unescape(raw_html.replace("\\/", "/"))
    for m in RAW_URL_RE.finditer(text):
        url = m.group(0).rstrip(".,;")
        if is_media_url(url) and url not in seen:
            seen.add(url)
            events.append(make_event("", "", url))
    return events, "links"
 
 
# -------------------- Build the playlist -----------------------------------
 
STRATEGIES = [parse_tables, parse_cards, parse_links]
 
 
def parse_events(raw_html, base, strict=True):
    soup = BeautifulSoup(raw_html, "html.parser")
    for strategy in STRATEGIES:
        try:
            events, name = strategy(soup, raw_html, base)
        except Exception as exc:
            print(f"  strategy {strategy.__name__} crashed: {exc}")
            continue
        if events:
            return events, name
    if strict:
        raise ValueError("No events found by any strategy.")
    return [], None
 
 
def to_m3u(events):
    lines = ["#EXTM3U"]
    for ev in events:
        lines.append(f'#EXTINF:-1 group-title="{ev["category"]}",{ev["title"]}')
        lines.append(ev["url"])
    return "\n".join(lines) + "\n"
 
 
def same_site(url, root):
    def host(u):
        return re.sub(r"^www\.", "", urlparse(u).netloc.lower())
    return host(url) == host(root)
 
 
def crawl_site(session):
    start = PAGE_URL.split("#")[0]
    queue = [(start, 0, "")]            # (url, depth, category hint)
    visited = {start}
    all_events, pages = [], 0
 
    while queue and pages < CRAWL_MAX_PAGES:
        url, depth, hint = queue.pop(0)
        try:
            resp = session.get(url, headers={"User-Agent": USER_AGENT}, timeout=REQUEST_TIMEOUT)
            resp.raise_for_status()
            if "html" not in resp.headers.get("Content-Type", "html").lower():
                continue
        except Exception as exc:
            if url == start:             # the start page itself must work
                raise RuntimeError(f"Could not load start page {url}: {exc}") from exc
            continue
        pages += 1
 
        events, strat = parse_events(resp.text, url, strict=False)
        soup = BeautifulSoup(resp.text, "html.parser")
 
        if hint:                         # category taken from the link that led here
            for ev in events:
                if ev["category"] == DEFAULT_CATEGORY:
                    ev["category"] = hint
        if len(events) == 1 and strat == "links":     # single-event page: use the page title
            page_title = text_of(soup.find("h1")) or text_of(soup.title)
            if page_title:
                events[0]["title"] = page_title
        all_events += events
 
        if depth < CRAWL_MAX_DEPTH:
            for a in soup.find_all("a", href=True):
                link = normalize_url(a["href"], url)
                if not link:
                    continue
                link = link.split("#")[0]
                if (link in visited or not same_site(link, start)
                        or SKIP_LINK_RE.search(link) or MEDIA_RE.search(link)
                        or not link.startswith(("http://", "https://"))):
                    continue
                visited.add(link)
                label = hint
                if not label:
                    t = clean_category(text_of(a))
                    label = "" if t.lower() in GENERIC_LABELS else t
                queue.append((link, depth + 1, label))
        time.sleep(CRAWL_DELAY)
 
    return dedupe(all_events), pages
 
 
def debug_site(max_pages=12):
    """Print what the crawler actually sees on each page (for troubleshooting)."""
    queue, seen, n = [(PAGE_URL, 0)], {PAGE_URL}, 0
    with requests.Session() as session:
        while queue and n < max_pages:
            url, depth = queue.pop(0)
            try:
                r = session.get(url, headers={"User-Agent": USER_AGENT}, timeout=REQUEST_TIMEOUT)
            except Exception as exc:
                print(f"\n=== {url}\n  ERROR: {exc}")
                continue
            n += 1
            soup = BeautifulSoup(r.text, "html.parser")
            print(f"\n=== {url}")
            print(f"  status={r.status_code} type={r.headers.get('Content-Type')} bytes={len(r.text)}")
            print(f"  title: {text_of(soup.title)}")
            links = [normalize_url(a['href'], url) for a in soup.find_all('a', href=True)]
            links = [l.split('#')[0] for l in links if l]
            print(f"  links: {len(links)} total, {len([l for l in links if same_site(l, PAGE_URL)])} on this site")
            for tag in ("iframe", "video", "source", "embed", "object"):
                for el in soup.find_all(tag):
                    print(f"  <{tag}> {el.get('src') or el.get('data') or '(no src)'}")
            ext = [sc['src'] for sc in soup.find_all('script', src=True)]
            print(f"  scripts: {len(ext)} external, {len(soup.find_all('script', src=False))} inline")
            for sc in ext[:6]:
                print(f"    {sc}")
            text = html_lib.unescape(r.text.replace("\\/", "/"))
            found = []
            for m in RAW_URL_RE.finditer(text):
                u = m.group(0).rstrip(".,;")
                if not SKIP_LINK_RE.search(u) and u not in found:
                    found.append(u)
            print(f"  other URLs in the page source ({len(found)}):")
            for u in found[:15]:
                print(f"    {u}")
            words = {w: len(re.findall(re.escape(w), r.text, re.I)) for w in
                     ("player", "embed", "m3u8", "stream", "token", "fetch(", "api/")}
            print(f"  word counts: {words}")
            if depth < 1:
                for l in links:
                    if l not in seen and same_site(l, PAGE_URL) and not SKIP_LINK_RE.search(l):
                        seen.add(l)
                        queue.append((l, depth + 1))
 
 
def build_playlist():
    if CRAWL:
        with requests.Session() as session:
            events, pages = crawl_site(session)
        if not events:
            raise ValueError(f"No events found on {pages} page(s) of the site.")
        return to_m3u(events), len(events), f"crawl ({pages} pages)"
 
    resp = requests.get(PAGE_URL, headers={"User-Agent": USER_AGENT}, timeout=REQUEST_TIMEOUT)
    resp.raise_for_status()
    events, strategy = parse_events(resp.text, PAGE_URL)
    return to_m3u(events), len(events), strategy
 
 
# -------------------- Server -----------------------------------------------
 
def refresh_loop():
    global _playlist, _last_strategy
    while True:
        stamp = time.strftime("%H:%M:%S")
        try:
            new_playlist, count, strategy = build_playlist()
            with _lock:
                _playlist = new_playlist
            print(f"[{stamp}] Updated: {count} events via {strategy}")
            if _last_strategy and strategy.split(" ")[0] != _last_strategy.split(" ")[0]:
                print(f"[{stamp}] Note: site layout seems to have changed "
                      f"({_last_strategy} -> {strategy})")
            _last_strategy = strategy
        except Exception as exc:
            print(f"[{stamp}] Refresh failed, keeping old playlist: {exc}")
        time.sleep(REFRESH_MINUTES * 60)
 
 
class Handler(BaseHTTPRequestHandler):
    def do_GET(self):
        with _lock:
            body = _playlist.encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/x-mpegurl")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Cache-Control", "no-cache")
        self.end_headers()
        self.wfile.write(body)
 
    def log_message(self, *args):
        pass
 
 
if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", help="parse a saved HTML file, print the playlist, and exit")
    ap.add_argument("--out", help="build the playlist once, save it to this file, and exit "
                                  "(used by GitHub Actions)")
    ap.add_argument("--debug", action="store_true",
                    help="print what the crawler sees on the first pages, then exit")
    args = ap.parse_args()
 
    if args.debug:
        debug_site()
        sys.exit(0)
 
    if args.out:
        try:
            playlist, count, strategy = build_playlist()
        except Exception as exc:
            print(f"FAILED: {exc}")
            sys.exit(1)
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(playlist)
        print(f"Saved {count} events to {args.out} via {strategy}")
        sys.exit(0)
 
    if args.file:
        with open(args.file, encoding="utf-8") as f:
            evs, strat = parse_events(f.read(), PAGE_URL)
        print(f"# strategy: {strat}, {len(evs)} events", file=sys.stderr)
        print(to_m3u(evs), end="")
        sys.exit(0)
 
    threading.Thread(target=refresh_loop, daemon=True).start()
    print(f"Reading {PAGE_URL} every {REFRESH_MINUTES} min")
    print(f"Playlist at http://localhost:{PORT}/playlist.m3u")
    ThreadingHTTPServer(("0.0.0.0", PORT), Handler).serve_forever()
 
