#!/usr/bin/env python3
"""Read-only validation of the prepared publication package, not a Lean check."""
from __future__ import annotations
import hashlib
import json
import sys
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
IGNORED_PARTS = {'.git', '.lake', '.verification-logs', '__pycache__'}

def main() -> int:
    inventory = ROOT / 'PUBLICATION_INVENTORY.json'
    try:
        records = json.loads(inventory.read_text(encoding='utf-8'))
        if not isinstance(records, list):
            raise ValueError('Expected an inventory list.')
        expected = {'PUBLICATION_INVENTORY.json'}
        errors: list[str] = []
        for record in records:
            name = record['path']
            relative = PurePosixPath(name)
            if relative.is_absolute() or '..' in relative.parts or name in expected:
                raise ValueError(f'Unsafe or duplicate inventory path: {name}')
            expected.add(name)
            path = ROOT.joinpath(*relative.parts)
            if path.is_symlink() or any(parent.is_symlink() for parent in path.parents if parent != ROOT.parent):
                errors.append(f'Symlink not permitted: {name}')
                continue
            if not path.is_file():
                errors.append(f'Missing file: {name}')
                continue
            data = path.read_bytes()
            if len(data) != record['bytes']:
                errors.append(f'Size mismatch: {name}')
            if hashlib.sha256(data).hexdigest() != record['sha256']:
                errors.append(f'Hash mismatch: {name}')
        extras: list[str] = []
        for path in ROOT.rglob('*'):
            parts = path.relative_to(ROOT).parts
            if any(part in IGNORED_PARTS for part in parts) or path.name == '.DS_Store':
                continue
            if not path.is_file():
                continue
            name = path.relative_to(ROOT).as_posix()
            if name not in expected:
                extras.append(name)
        if extras:
            errors.append('Files not in publication allowlist (do not stage): ' + ', '.join(sorted(extras)))
        if errors:
            print('\n'.join(errors), file=sys.stderr)
            return 1
        print(f'PASS: {len(records)} inventoried files match sizes and SHA-256 hashes; inventory is self-exempt.')
        print('This checks package identity only; it does not run Lean or establish remote publication.')
        return 0
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f'Inventory check failed: {exc}', file=sys.stderr)
        return 2

if __name__ == '__main__':
    raise SystemExit(main())
