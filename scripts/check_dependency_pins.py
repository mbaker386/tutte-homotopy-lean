#!/usr/bin/env python3
"""Verify dependency checkouts against the existing Lake manifest."""
from pathlib import Path
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def main() -> int:
    data = json.loads((ROOT/'lake-manifest.json').read_text())
    errors = []
    for pkg in data['packages']:
        if pkg.get('type') != 'git':
            errors.append(f"Unsupported dependency kind for {pkg['name']}")
            continue
        directory = ROOT / data['packagesDir'] / pkg['name']
        try:
            rev = subprocess.check_output(['git','-C',str(directory),'rev-parse','HEAD'], text=True).strip()
            # Generated untracked build/cache files are expected; tracked changes are not.
            dirty = subprocess.check_output(['git','-C',str(directory),'status','--porcelain','--untracked-files=no'], text=True).strip()
        except (OSError, subprocess.CalledProcessError) as exc:
            errors.append(f"Cannot inspect {pkg['name']}: {exc}")
            continue
        if rev != pkg['rev'] or dirty:
            errors.append(f"Dependency mismatch/modified: {pkg['name']} HEAD={rev}; tracked status={dirty!r}")
        else:
            print(f"PASS: {pkg['name']} {rev}")
    for err in errors:
        print(err, file=sys.stderr)
    return 1 if errors else 0

if __name__ == '__main__':
    raise SystemExit(main())
