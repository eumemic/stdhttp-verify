"""Random multi-way splits of every seed; reports any change in interpretation, grouped by direction.

Usage: python3 -I harness/randsplit.py <garden_tools_dir> <host> <port> [trials_per_seed]
"""
import os
import random
import sys
from collections import Counter
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(__file__))
import segment  # noqa: E402
import seeds  # noqa: E402

trials = int(sys.argv[4]) if len(sys.argv) > 4 else 20
random.seed(1234)
jobs = []
for name, p in seeds.SEEDS.items():
    for _ in range(trials):
        cuts = sorted(random.sample(range(1, len(p)), k=min(len(p) - 1, random.randint(1, 4))))
        pieces = [p[a:b] for a, b in zip([0] + cuts, cuts + [len(p)])]
        jobs.append((name, pieces))
base = {n: segment.describe(segment.roundtrip([p])) for n, p in seeds.SEEDS.items()}


def run(job):
    name, pieces = job
    return name, pieces, segment.describe(segment.roundtrip(pieces))


def kind(res):
    return "ACCEPT" if any(r.startswith("ACCEPT") for r in res) else "REJECT"


directions = Counter()
odd = []
with ThreadPoolExecutor(16) as ex:
    for name, pieces, res in ex.map(run, jobs):
        if res != base[name]:
            d = f"{kind(base[name])}->{kind(res)}"
            directions[d] += 1
            if d != "ACCEPT->REJECT" or kind(res) == "ACCEPT":
                odd.append((name, pieces, base[name], res))
print(f"{len(jobs)} random splits; changed: {dict(directions)}")
for name, pieces, b, r in odd[:20]:
    print(f"  {name}: {pieces!r}\n     single={b}\n     split ={r}")
