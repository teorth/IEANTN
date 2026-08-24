#!/usr/bin/env bash
# Run Comparator against one node's solution.
#
# Usage: scripts/verify-comparator.sh <Family>.<version>
#
# This script runs UNTRUSTED code: elaborating a contributor's Lean solution can execute arbitrary
# code. It must therefore never run in a job that holds a write token. See
# .github/workflows/verify.yml, which splits verification (no write access) from recording the
# receipt (no untrusted code).
#
# Requires Linux with Landlock, plus cargo, git, go, lake and python3. It does not run on Windows
# or macOS; WSL2 works for debugging.
set -euo pipefail

node=${1:?usage: verify-comparator.sh <Family>.<version>}
repository_root=$(cd "$(dirname "$0")/.." && pwd)
solution_dir="$repository_root/Solutions/$node"
config="$solution_dir/comparator.json"

[ -d "$solution_dir" ] || { echo "error: no solution at Solutions/$node" >&2; exit 1; }
[ -f "$config" ] || { echo "error: no $config" >&2; exit 1; }

cache_root=${IEANTN_COMPARATOR_CACHE:-"$repository_root/.cache/comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

# Pinned trusted tooling. `lean4export` is pinned to the tag matching this repository's toolchain;
# the others are the revisions the Palomar registry uses. Bump deliberately, never automatically:
# these four are the trusted base of every receipt.
comparator_commit=10dd2b33dc43751af3257f4d684535375306f162
lean4export_commit=cacf989bd75f608700820f6afc595f32e7a99a4d
# The toolchain the pin above is for. `ieantn.py check-pins` compares this against `lean-toolchain`,
# so a Mathlib bump that leaves the pin behind fails at the bump -- when the fix is obvious -- rather
# than weeks later at the next verification, where it would look like verification is broken.
lean4export_toolchain=leanprover/lean4:v4.34.0-rc2
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required in cargo git go lake python3; do
  command -v "$required" >/dev/null 2>&1 || { echo "error: $required is required" >&2; exit 1; }
done

python3 - "$config" <<'PY'
import json, pathlib, sys
path = pathlib.Path(sys.argv[1])
config = json.loads(path.read_text(encoding="utf-8"))
if config.get("enable_nanoda") is not True:
    sys.exit(f"error: {path}: enable_nanoda must be exactly true; the NanoDa replay is required")
permitted = set(config.get("permitted_axioms") or [])
allowed = {"propext", "Quot.sound", "Classical.choice"}
if not permitted <= allowed:
    sys.exit(f"error: {path}: permitted_axioms may only contain {sorted(allowed)}")
PY

checkout_exact() {
  local repository=$1 destination=$2 commit=$3
  [ -d "$destination/.git" ] || git clone --filter=blob:none "$repository" "$destination"
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

mkdir -p "$cache_root" "$bin_dir"
checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$export_toolchain" ]; then
  echo "error: this repository is on $project_toolchain but the pinned lean4export is on" >&2
  echo "       $export_toolchain. Update lean4export_commit to the matching tag, then check" >&2
  echo "       that Comparator and NanoDa still understand the export format." >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"
GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$solution_dir"
lake exe cache get || true
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$bin_dir/landrun" \
  lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json

echo "comparator accepted Solutions/$node"
