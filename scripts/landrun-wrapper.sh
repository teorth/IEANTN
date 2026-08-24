#!/usr/bin/env bash
set -euo pipefail

# Landrun's current CLI needs an explicit outer `--` before the sandboxed
# command. Comparator constructs Landrun's options itself but does not add that
# delimiter. Without it, Landrun consumes lean4export's own `--` separator.
landrun_binary=${PALOMAR_LANDRUN_BIN:?PALOMAR_LANDRUN_BIN must name the pinned Landrun binary}
landrun_options=()

while [ "$#" -gt 0 ]; do
  case "$1" in
    --best-effort|-ldd|--ldd|-add-exec|--add-exec|--unrestricted-filesystem|--unrestricted-network|--unrestricted-scoped|--ignore-missing|--log-disable-originating|--log-enable-subprocesses|--log-disable-subdomains)
      landrun_options+=("$1")
      shift
      ;;
    --log-level|--ro|--rox|--rw|--rwx|--unix|--bind-tcp|--connect-tcp|--env)
      if [ "$#" -lt 2 ]; then
        echo "error: Landrun option $1 is missing its value" >&2
        exit 2
      fi
      landrun_options+=("$1" "$2")
      shift 2
      ;;
    -*)
      echo "error: unrecognized Landrun option $1; update scripts/landrun-wrapper.sh" >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [ "$#" -eq 0 ]; then
  echo "error: Comparator supplied no sandboxed command" >&2
  exit 2
fi

exec "$landrun_binary" "${landrun_options[@]}" -- "$@"
