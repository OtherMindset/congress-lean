"""Re-fetch every posted file this project was built from (manifest_sources.json) from othermindset.com and check
its SHA-256. Writes sources/<post id>.lean exactly as the site stores the text (no final newline added).
Fetches each post once, 0.2 s apart. Exits 1 on any mismatch."""
import hashlib, json, os, sys, time, urllib.request
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.makedirs(os.path.join(root, "sources"), exist_ok=True)
bad = 0
for rec in json.load(open(os.path.join(root, "manifest_sources.json"))):
    url = f"https://othermindset.com/api/work/oeis-new-terms/{rec['post_id']}"
    req = urllib.request.Request(url, headers={"User-Agent": "lt2d-fetch-sources/1.0"})
    post = json.load(urllib.request.urlopen(req, timeout=60))["post"]
    b = post["text"].encode("utf-8")
    ok = hashlib.sha256(b).hexdigest() == rec["sha256"] == post["code_sha256"]
    bad += not ok
    open(os.path.join(root, "sources", rec["post_id"] + ".lean"), "wb").write(b)
    print(("OK  " if ok else "FAIL"), rec["post_id"])
    time.sleep(0.2)
sys.exit(1 if bad else 0)
