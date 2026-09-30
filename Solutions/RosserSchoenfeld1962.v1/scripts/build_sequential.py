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


def source(module: str) -> Path | None:
    relative = Path(module.replace(".", "/") + ".lean")
    if module == "Solution" or module.startswith("RS12."):
        return ROOT / relative
    if module.startswith("LeanCert."):
        return LEAN_CERT / relative
    return None


def build_order() -> list[str]:
    seen: set[str] = set()
    order: list[str] = []

    def visit(module: str) -> None:
        if module in seen:
            return
        seen.add(module)
        path = source(module)
        if path is None:
            return  # Mathlib and the small core conclusion are handled by Lake.
        for line in path.read_text().splitlines():
            match = re.fullmatch(r"(?:public |meta )*import\s+(.+)", line)
            if match:
                for dependency in match[1].split("--")[0].split():
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
        with log_path.open("w") as log:
            result = subprocess.run(
                ["lake", "build", module], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT
            )
        if result.returncode:
            print(log_path.read_text(), end="")
            raise SystemExit(result.returncode)
        print(f"  passed in {time.monotonic() - start:.1f}s", flush=True)
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
