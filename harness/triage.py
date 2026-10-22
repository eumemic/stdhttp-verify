"""Print each discrepant record: lean's interpretation vs. the other servers, grouped by identical result."""
import json, sys
from collections import defaultdict

path = sys.argv[1]
only = set(sys.argv[2:])
for line in open(path):
    rec = json.loads(line)
    name = rec.get("seed") or f"iter{rec.get('iteration')}"
    if not rec["disagree"] or (only and name not in only):
        continue
    print(f"=== {name}  others_agreement={rec['others_agreement']}  odd={rec['lean_is_odd_one_out']}")
    print("    payload:", " | ".join(rec["payload_repr"])[:300])
    lean = rec["results"]["lean_stdhttp"]
    print("    LEAN   :", " || ".join(lean)[:400] or "(no response)")
    groups = defaultdict(list)
    for srv, res in rec["results"].items():
        if srv != "lean_stdhttp":
            groups[" || ".join(res)[:400] or "(no response)"].append(srv + ("*" if srv in rec["disagree"] else ""))
    for desc, srvs in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        print(f"    {','.join(srvs):40s}: {desc}")
