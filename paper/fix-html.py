#!/usr/bin/env python3
"""Check the make4ht HTML and insert the formats banner.

MathJax macros are emitted by html.cfg. This script refuses a page that
lost them, and restores the banner that tex4ht does not know about.
"""

import re
import sys
from pathlib import Path

BANNER = """<nav class="pdf-banner" aria-label="Formats">
<a href="main.pdf">PDF of this note</a>
<span class="pdf-banner-sep">·</span>
<span>HTML reading copy</span>
<span class="pdf-banner-sep">·</span>
<a href="once-or-twice.html">Once or Twice</a>
<span class="pdf-banner-sep">·</span>
<a href="once-or-twice-encyclopedia.html">Once or Twice (encyclopedia)</a>
</nav>
"""

# Two backslashes in the HTML source, so the JavaScript string value is \Box.
REQUIRED = (
    'Nec: "\\\\Box"',
    'Pos: "\\\\Diamond"',
    'exE: "\\\\exists^{E}"',
    'allE: "\\\\forall^{E}"',
    'necImp: "\\\\supset_{N}"',
    'valid: ["\\\\lfloor #1 \\\\rfloor", 1]',
)


def main() -> None:
    path = Path(sys.argv[1] if len(sys.argv) > 1 else "main.html")
    html = path.read_text()
    missing = [item for item in REQUIRED if item not in html]
    if missing:
        raise SystemExit("MathJax config is missing: " + ", ".join(missing))
    if 'class="pdf-banner"' not in html:
        html = html.replace("<body>", "<body>\n" + BANNER, 1)
    # tex4ht sometimes stretches "7 January 2025" with runs of spaces.
    html = re.sub(
        r"7(?:\s|\u00a0)+January(?:\s|\u00a0)+2025",
        "7 January 2025",
        html,
    )
    path.write_text(html)
    print("html ok", path)


if __name__ == "__main__":
    main()
