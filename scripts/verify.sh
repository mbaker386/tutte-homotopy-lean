#!/usr/bin/env bash
# Reproduce the mathematical checks without changing proofs or dependency pins.
set -euo pipefail
ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
for cmd in python3 git lake; do
  if ! command -v "$cmd" >/dev/null 2>&1; then
    printf 'Required command not found: %s\n' "$cmd" >&2
    exit 127
  fi
done
mkdir -p .verification-logs
LOG_DIR="$(mktemp -d "$ROOT/.verification-logs/run-XXXXXXXX")"
printf 'Verification logs: %s\n' "$LOG_DIR"
run() {
  local log="$1"
  shift
  printf '\n$'; printf ' %q' "$@"; printf '\n'
  "$@" 2>&1 | tee "$LOG_DIR/$log"
}
run source-before.log python3 scripts/check_source_snapshot.py
run lean-version.log lake env lean --version
if ! grep -Eq '^Lean \(version 4\.34\.0-rc2([, )]|$)' "$LOG_DIR/lean-version.log"; then
  printf 'Unexpected Lean version; do not update this snapshot to bypass the check.\n' >&2
  exit 1
fi
run mathlib-cache.log lake exe cache get
run pins-before.log python3 scripts/check_dependency_pins.py
targets=()
while IFS= read -r module; do
  if [[ -n "$module" ]]; then targets+=("$module"); fi
done < scripts/build-targets.txt
run target-build.log lake build "${targets[@]}"
run path-statement.log lake env lean audit/StatementAudit.lean
run path-boundary.log lake env lean Audit.lean
run homotopy-statement.log lake env lean homotopy/audit/StatementAudit.lean
run semantic-axioms.log lake env lean homotopy/audit/SemanticsAudit.lean
run allowed-axioms.log python3 scripts/check_target_axioms.py "$LOG_DIR"
run path-replay.log lake env lean audit/KernelReplay.lean
run homotopy-replay.log lake env lean homotopy/audit/FinalKernelReplay.lean
run pins-after.log python3 scripts/check_dependency_pins.py
run source-after.log python3 scripts/check_source_snapshot.py
printf '\nAll requested verification commands passed. Logs: %s\n' "$LOG_DIR"
