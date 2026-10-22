"""Send the failing split cases to every Garden origin (runs in the driver container)."""
import json
import sys

sys.path.insert(0, "/harness")
sys.path.insert(0, "/garden/tools")  # targets.py locates its config via sys.path[0]
from fanout import fanout  # noqa: E402
from targets import ORIGIN_DICT  # noqa: E402
from driver import describe  # noqa: E402
import seeds  # noqa: E402

cases = {}
for line in open("/out/segment.jsonl"):
    m = json.loads(line)
    cases.setdefault(m["seed"], m["split_at"])  # first failing split position per seed
servers = [ORIGIN_DICT[n] for n in sorted(ORIGIN_DICT)]
for name, k in cases.items():
    p = seeds.SEEDS[name]
    results = fanout([p[:k], p[k:]], servers)
    print(f"{name} split at {k}:")
    for s, res in zip(servers, results):
        print(f"    {s.name:14s} {' || '.join(describe(r) for r in res)[:110]}")
