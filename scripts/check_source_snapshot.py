#!/usr/bin/env python3
"""Check byte identity of the published proof snapshot; does not run Lean."""
from pathlib import Path
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parents[1]

def main() -> int:
    data = json.loads((ROOT / 'SOURCE_SNAPSHOT.json').read_text())
    failures = []
    for entry in data['files']:
        p = ROOT / entry['path']
        if p.is_symlink() or not p.is_file():
            failures.append(f"Missing or symlinked source: {entry['path']}")
            continue
        b = p.read_bytes()
        if len(b) != entry['bytes'] or hashlib.sha256(b).hexdigest() != entry['sha256']:
            failures.append(f"Changed source: {entry['path']}")
    expected = {e['path'] for e in data['files']
                if e['path'].startswith('TutteFormalization/') and e['path'].endswith('.lean')}
    actual = {p.relative_to(ROOT).as_posix() for p in (ROOT/'TutteFormalization').rglob('*.lean')}
    if actual != expected:
        failures.append(f"Project source set differs: extra={sorted(actual-expected)}, missing={sorted(expected-actual)}")
    for item in failures:
        print(item, file=sys.stderr)
    if failures:
        print('Do not regenerate hashes to conceal an unreviewed mathematical change.', file=sys.stderr)
        return 1
    print(f"PASS: {len(data['files'])} preserved proof/audit/configuration files match the reviewed snapshot.")
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
