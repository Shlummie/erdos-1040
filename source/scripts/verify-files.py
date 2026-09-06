#!/usr/bin/env python3
"""Verify the published file manifest without building Lean or using a network."""
from pathlib import Path
import hashlib
import json
import sys

root = Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8'))
errors = []
for entry in manifest['files']:
    path = root / entry['path']
    if not path.resolve().is_relative_to(root.resolve()):
        errors.append('Invalid path: ' + entry['path'])
    elif not path.is_file():
        errors.append('Missing: ' + entry['path'])
    elif hashlib.sha256(path.read_bytes()).hexdigest() != entry['sha256']:
        errors.append('Changed: ' + entry['path'])
if errors:
    print('\n'.join(errors))
    sys.exit(1)
print('PASS: all ' + str(len(manifest['files'])) + ' published file hashes match.')
