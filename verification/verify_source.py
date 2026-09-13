"""Check exact public-source byte identities, not mathematical correctness."""
import hashlib
import json
from pathlib import Path
root = Path(__file__).resolve().parents[1]
m = json.loads((root / 'SOURCE-MANIFEST.json').read_text(encoding='utf-8'))
for f in m['files']:
    data = (root / f['destination']).read_bytes()
    git_blob = hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()
    if len(data) != f['bytes'] or hashlib.sha256(data).hexdigest() != f['sha256'] or git_blob != f['source_blob']:
        raise SystemExit('FAIL: ' + f['destination'])
print(json.dumps({'result':'PASS','source_files':len(m['files'])}))
