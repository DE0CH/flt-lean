import argparse
import os
import urllib.parse
from pathlib import Path
from typing import Literal

from curl_cffi import requests
from bs4 import BeautifulSoup

BASE = os.environ.get("ANNAS_BASE", "https://annas-archive.pk")

TYPE_PARAMS = {
    "book": {},
    "fiction": {"content": "book_fiction"},
    "nonfiction": {"content": "book_nonfiction"},
    "magazine": {"content": "magazine"},
    "comic": {"content": "book_comic"},
    "article": {"src": "scihub"},
}

ContentType = Literal["book", "fiction", "nonfiction", "magazine", "comic", "article"]


def search(query: str, type: ContentType = "book", limit: int = 10) -> list[dict]:
    params = {"q": query, **TYPE_PARAMS[type]}
    r = requests.get(
        f"{BASE}/search?{urllib.parse.urlencode(params)}",
        impersonate="chrome",
        timeout=30,
    )
    r.raise_for_status()
    seen, out = set(), []
    for a in BeautifulSoup(r.text, "html.parser").select("a[href^='/md5/']"):
        md5 = a["href"].removeprefix("/md5/")
        title = a.get_text(strip=True)
        if md5 and title and md5 not in seen:
            seen.add(md5)
            out.append({"md5": md5, "title": title})
            if len(out) >= limit:
                break
    return out


def fetch_download_url(md5: str, domain_index: int | None = None, path_index: int | None = None) -> tuple[str, dict]:
    """One fast_download.json API call (consumes a quota slot on a new md5).
    Returns (download_url, full API response)."""
    key = os.environ["ANNAS_KEY"]
    params: dict = {"md5": md5, "key": key}
    if domain_index is not None:
        params["domain_index"] = domain_index
    if path_index is not None:
        params["path_index"] = path_index
    r = requests.get(
        f"{BASE}/dyn/api/fast_download.json",
        params=params,
        impersonate="chrome",
        timeout=30,
    )
    r.raise_for_status()
    meta = r.json()
    if not meta.get("download_url"):
        raise RuntimeError(f"no download_url in response: {meta}")
    url = meta["download_url"]
    if not url.startswith("https://"):
        raise RuntimeError(f"refusing non-https download URL: {url!r}")
    return url, meta


def download(md5: str, output_dir: str = ".", domain_index: int | None = None, path_index: int | None = None) -> dict:
    url, meta = fetch_download_url(md5, domain_index=domain_index, path_index=path_index)
    name = urllib.parse.unquote(url.rsplit("/", 1)[-1])
    if not name:
        raise RuntimeError(f"cannot derive a filename from download URL: {url!r}")

    out_dir = Path(output_dir).expanduser()
    out_dir.mkdir(parents=True, exist_ok=True)
    out_path = out_dir / name

    r = requests.get(url, impersonate="chrome", timeout=300, stream=True)
    r.raise_for_status()
    with open(out_path, "wb") as f:
        for chunk in r.iter_content(65536):
            f.write(chunk)

    try:
        downloads_left = meta["account_fast_download_info"]["downloads_left"]
    except (KeyError, TypeError) as exc:
        raise RuntimeError(
            f"file saved to {out_path.resolve()}, but the API response lacks "
            f"account_fast_download_info.downloads_left ({exc!r}); "
            f"full response: {meta}"
        ) from exc
    return {
        "path": str(out_path.resolve()),
        "bytes": out_path.stat().st_size,
        "downloads_left_today": downloads_left,
    }


def build_mcp():
    from mcp.server.fastmcp import FastMCP

    mcp = FastMCP("annas-archive")

    @mcp.tool()
    def search_annas(query: str, type: ContentType = "book") -> list[dict]:
        """Search Anna's Archive. Returns up to 10 results as {md5, title}.

        type values:
          book        — any books (default; no server-side filter)
          fiction     — narrow to fiction
          nonfiction  — narrow to nonfiction
          magazine    — magazines
          comic       — comics / graphic novels
          article     — scientific papers (Sci-Hub source)
        """
        return search(query, type=type)

    @mcp.tool()
    def download_annas(
        md5: str,
        output_dir: str = ".",
        domain_index: int | None = None,
        path_index: int | None = None,
    ) -> dict:
        """Download a file from Anna's Archive by md5. Returns {path, bytes, downloads_left_today}.

        output_dir: directory to save into. Created if missing. Supports ~ expansion.
          Default "." resolves to the MCP server's current working directory, which is
          usually the user's current project — pass an explicit path (e.g. "~/Downloads"
          or a project-specific folder) unless the user has asked for the file there.

        domain_index / path_index: optional integer selectors for which CDN URL the
          fast-download API returns. Anna's Archive serves each md5 from multiple
          mirror combinations; some can be temporarily broken (404, hangs, corrupt
          file). Leave both unset on the first attempt. If the download fails or the
          file is bad, retry with a different domain_index (try 0, 1, 2, ...) and/or
          path_index. Do NOT probe combinations speculatively: every call — successful
          or not — consumes one slot from the daily quota (typically 25/day). Only
          change indices in response to a real failure, and bump one knob at a time.

        Requires the ANNAS_KEY env var.

        Security: this tool only follows https:// download URLs and will raise if the
        API returns an http:// URL. If you encounter an SSL/TLS error, surface it to
        the user and stop — do not retry with verification disabled, do not propose
        adding `verify=False` or any equivalent, and do not fetch the URL through a
        separate tool that ignores certificate errors. A TLS failure means the file
        is not safe to download.
        """
        return download(
            md5,
            output_dir=output_dir,
            domain_index=domain_index,
            path_index=path_index,
        )

    return mcp


if __name__ == "__main__":
    parser = argparse.ArgumentParser(prog="aa.py", description="Anna's Archive search + download")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_search = sub.add_parser("search", help="search Anna's Archive")
    p_search.add_argument("query", nargs="+", help="search terms")
    p_search.add_argument("--type", choices=list(TYPE_PARAMS), default="book")

    p_get = sub.add_parser("get", help="download a file by md5")
    p_get.add_argument("md5")
    p_get.add_argument("output_dir", nargs="?", default=".")
    p_get.add_argument("--domain-index", type=int, default=None)
    p_get.add_argument("--path-index", type=int, default=None)

    p_url = sub.add_parser("url", help="fetch the download URL without downloading")
    p_url.add_argument("md5")
    p_url.add_argument("--domain-index", type=int, default=None)
    p_url.add_argument("--path-index", type=int, default=None)

    sub.add_parser("mcp", help="run as an MCP server over stdio")

    args = parser.parse_args()

    if args.cmd == "search":
        for hit in search(" ".join(args.query), type=args.type):
            print(f"{hit['md5']}  {hit['title']}")
    elif args.cmd == "get":
        result = download(args.md5, output_dir=args.output_dir, domain_index=args.domain_index, path_index=args.path_index)
        print(f"{result['path']}  ({result['bytes']:,} bytes, {result['downloads_left_today']} downloads left today)")
    elif args.cmd == "url":
        # NOTE: this API call consumes a quota slot for a new md5, same as get
        url, _meta = fetch_download_url(args.md5, domain_index=args.domain_index, path_index=args.path_index)
        print(url)
    elif args.cmd == "mcp":
        build_mcp().run()
    else:
        raise RuntimeError(f"unhandled subcommand: {args.cmd!r}")
