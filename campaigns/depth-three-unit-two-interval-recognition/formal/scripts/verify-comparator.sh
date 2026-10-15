#!/usr/bin/env bash
set -euo pipefail

# Adapted from PalomarTemplate: use this toolchain's comparator and bundled kernels.
project_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$project_root"

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator (Linux sandbox)" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    exit 1
  fi
done

temporary=$(mktemp -d "${TMPDIR:-/tmp}/bfs-comparator.XXXXXX")
trap 'rm -rf "$temporary"' EXIT
python3 - comparator.json "$temporary" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, temporary, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text())
if "external_kernels" in config:
    raise SystemExit("error: external_kernels is not a submitter field")
standard = {"propext", "Quot.sound", "Classical.choice"}
if not set(config["permitted_axioms"]) <= standard:
    raise SystemExit("error: comparator.json may permit only the three foundational axioms")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
Path(temporary, "strict.json").write_text(json.dumps(config) + "\n")
# This temporary allowance verifies the open template, never certifies a proof.
config["permitted_axioms"].append("sorryAx")
# con-ron declines every sorryAx in --verified mode regardless of the policy, so
# the open pass replays through nanoda and Lean's kernel; the strict pass uses all.
del config["external_kernels"]["con-ron"]
Path(temporary, "open.json").write_text(json.dumps(config) + "\n")
PY

status=0
lake comparator --config "$temporary/strict.json" > "$temporary/strict.log" 2>&1 || status=$?
cat "$temporary/strict.log"
if [ "$status" -eq 0 ]; then
  echo "Proof accepted: statement matches and all kernels accept under the strict axiom policy."
elif [ "$status" -eq 1 ] && grep -qxF "error: Illegal axiom detected: 'sorryAx'" "$temporary/strict.log"; then
  # Comparator stops at its first illegal axiom; a second full run rules out others.
  lake comparator --config "$temporary/open.json"
  echo "Open question verified: statement matches; sorryAx is the only forbidden axiom. No proof certified."
else
  echo "error: comparator failed for a reason other than the open proof placeholder" >&2
  exit 1
fi
