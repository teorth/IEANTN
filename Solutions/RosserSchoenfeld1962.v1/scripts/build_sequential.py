#!/usr/bin/env python3
"""Build the RS12 import closure one module at a time, retaining Lake's normal caches.

Run from any directory after `lake update` / `lake exe cache get` in the solution.
The certificate shards are memory-intensive; serial builds avoid compiling all twelve
independent factorial shards at once. Logs are local build output, not verification receipts.
"""

from pathlib import Path
import re
import subprocess
import time

ROOT = Path(__file__).resolve().parent.parent
LEAN_CERT = ROOT / ".lake/packages/leancert"
_IMPORT = re.compile(
    r"(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S(?:.*\S)?)"
)


def source(module: str, root: Path = ROOT, leancert: Path = LEAN_CERT) -> Path | None:
    relative = Path(module.replace(".", "/") + ".lean")
    if module == "Solution" or module.startswith("RS12."):
        return root / relative
    if module.startswith("LeanCert."):
        return leancert / relative
    return None


def visible_lean(text: str) -> str:
    """Lean source with comments and string contents removed.

    Import lines are otherwise indistinguishable from the same text in a block
    comment or a docstring. Block comments nest, and a `/-` inside a string is
    not a comment. Newlines stay put so the following line scan still sees one
    declaration per line.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("--", i):
            newline = text.find("\n", i)
            i = n if newline < 0 else newline
            continue
        if text.startswith("/-", i):
            i += 2
            depth = 1
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    if text[i] == "\n":
                        out.append("\n")
                    i += 1
            continue
        if text[i] == '"':
            out.append('"')
            i += 1
            while i < n:
                if text[i] == "\\":
                    i += 2 if i + 1 < n else 1
                    continue
                if text[i] == '"':
                    out.append('"')
                    i += 1
                    break
                if text[i] == "\n":
                    out.append("\n")
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def imported_modules(text: str) -> list[str]:
    modules: list[str] = []
    for line in visible_lean(text).splitlines():
        match = _IMPORT.fullmatch(line.strip())
        if match:
            modules.extend(match.group(1).split())
    return modules


def build_order(root: Path = ROOT, leancert: Path = LEAN_CERT) -> list[str]:
    seen: set[str] = set()
    order: list[str] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        path = source(module, root, leancert)
        if path is None:
            return  # Mathlib and the small core conclusion are handled by Lake.
        # Locale encoding is ASCII under LC_ALL=C; these files contain ψ and other
        # non-ASCII tokens, and read_text() would then abort the serial build.
        for dependency in imported_modules(path.read_text(encoding="utf-8")):
            visit(dependency)
        order.append(module)

    visit("Solution")
    return order


def main() -> None:
    log_dir = ROOT / ".lake/rs12-build-logs"
    log_dir.mkdir(parents=True, exist_ok=True)
    order = build_order()
    for number, module in enumerate(order, 1):
        log_path = log_dir / f"{module}.log"
        print(f"[{number}/{len(order)}] {module}", flush=True)
        start = time.monotonic()
        with log_path.open("w", encoding="utf-8") as log:
            result = subprocess.run(
                ["lake", "build", module], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT
            )
        if result.returncode:
            print(log_path.read_text(encoding="utf-8"), end="")
            raise SystemExit(result.returncode)
        print(f"  passed in {time.monotonic() - start:.1f}s", flush=True)
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
