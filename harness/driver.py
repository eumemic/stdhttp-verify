"""Differential driver: send payloads to HTTP Garden origins and record where lean_stdhttp disagrees.

Runs inside a container on the Garden's Docker network with the Garden repo mounted at /garden.
"""

import argparse
import base64
import json
import random
import sys
import time

sys.path.insert(0, "/garden/tools")

from diff import ErrorType, categorize_discrepancy  # noqa: E402
from fanout import fanout  # noqa: E402
from http1 import HTTPRequest, HTTPResponse  # noqa: E402
from mutations import mutate  # noqa: E402
from targets import ORIGIN_DICT  # noqa: E402

import seeds  # noqa: E402

LEAN = "lean_stdhttp"
IGNORED = {ErrorType.OK, ErrorType.RESPONSE_DISCREPANCY}


def describe(r: HTTPRequest | HTTPResponse) -> str:
    if isinstance(r, HTTPResponse):
        return f"REJECT {r.code.decode('latin1')}"
    hdrs = ", ".join(f"{k.decode('latin1')}: {v!r}" for k, v in r.headers)
    return f"ACCEPT {r.method!r} {r.uri!r} v{r.version.decode('latin1')} [{hdrs}] body={r.body!r}"


def evaluate(payload: list[bytes], servers: list) -> dict:
    results = fanout(payload, servers)
    by_name = {s.name: (s, res) for s, res in zip(servers, results)}
    lean_s, lean_r = by_name[LEAN]
    others = [n for n in by_name if n != LEAN]
    disagree: dict[str, str] = {}
    for name in others:
        s, res = by_name[name]
        et = categorize_discrepancy(lean_r, res, lean_s, s)
        if et not in IGNORED:
            disagree[name] = et.name
    # How much do the other servers agree among themselves?
    pairs = agree = 0
    for i, a in enumerate(others):
        for b in others[i + 1 :]:
            pairs += 1
            sa, ra = by_name[a]
            sb, rb = by_name[b]
            agree += categorize_discrepancy(ra, rb, sa, sb) in IGNORED
    flags = []
    lean_accepts = any(isinstance(r, HTTPRequest) for r in lean_r)
    rejecters = [n for n in others if not any(isinstance(r, HTTPRequest) for r in by_name[n][1])]
    if lean_accepts and len(rejecters) * 2 >= len(others):
        flags.append("lean-accepts-majority-rejects")
    accepters = [n for n in others if n not in rejecters]
    differing = [n for n in accepters if disagree.get(n) in ("REQUEST_DISCREPANCY", "STREAM_DISCREPANCY")]
    if lean_accepts and len(accepters) >= 2 and differing == accepters:
        consistent = all(
            categorize_discrepancy(by_name[a][1], by_name[b][1], by_name[a][0], by_name[b][0]) in IGNORED
            for i, a in enumerate(accepters) for b in accepters[i + 1 :]
        )
        if consistent:
            flags.append("lean-unique-interpretation")
    return {
        "flags": flags,
        "payload_b64": [base64.b64encode(p).decode() for p in payload],
        "payload_repr": [repr(p) for p in payload],
        "disagree": disagree,
        "others_agreement": round(agree / pairs, 2) if pairs else None,
        "lean_is_odd_one_out": len(disagree) == len(others) and pairs > 0 and agree == pairs,
        "results": {name: [describe(r) for r in res] for name, (_, res) in by_name.items()},
    }


def run_seeds(servers: list, out: str) -> None:
    with open(out, "w") as f:
        for name, payload in seeds.SEEDS.items():
            rec = evaluate([payload], servers)
            rec["seed"] = name
            f.write(json.dumps(rec) + "\n")
            flag = "ODD-ONE-OUT" if rec["lean_is_odd_one_out"] else ""
            if rec["disagree"]:
                print(f"{name:32s} lean disagrees with {sorted(rec['disagree'])} {flag}")


def run_fuzz(servers: list, out: str, iterations: int, seed: int) -> None:
    random.seed(seed)
    corpus = [[p] for p in seeds.SEEDS.values()]
    seen: set[frozenset] = set()
    seen_flags: set = set()
    start = time.time()
    with open(out, "w") as f, open(out.replace(".jsonl", "-flagged.jsonl"), "w") as flagged:
        for i in range(iterations):
            payload = random.choice(corpus)
            try:
                for _ in range(random.randint(1, 3)):
                    payload = mutate(payload)
            except (OverflowError, ValueError, RecursionError):
                continue  # the Garden's mutators can't parse some payloads (e.g. huge Content-Length)
            try:
                rec = evaluate(payload, servers)
            except Exception as e:  # a server crashed or the connection failed
                print(f"[{i}] error {e!r} on {payload!r}", file=sys.stderr)
                continue
            signature = frozenset(rec["disagree"].items())
            flag_key = (tuple(rec["flags"]), rec["results"][LEAN][0][:60] if rec["results"][LEAN] else "")
            if rec["flags"] and flag_key not in seen_flags:
                seen_flags.add(flag_key)
                rec["iteration"] = i
                flagged.write(json.dumps(rec) + "\n")
                flagged.flush()
                print(f"[{i}] FLAG {rec['flags']} {rec['payload_repr']!s:.200}")
            if signature and signature not in seen:
                seen.add(signature)
                corpus.append(payload)
                rec["iteration"] = i
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print(f"[{i}] new signature {sorted(rec['disagree'])} odd={rec['lean_is_odd_one_out']}")
            if i % 500 == 0:
                print(f"[{i}] {time.time() - start:.0f}s corpus={len(corpus)} signatures={len(seen)}", file=sys.stderr)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("mode", choices=["seeds", "fuzz"])
    ap.add_argument("--out", required=True)
    ap.add_argument("--iterations", type=int, default=5000)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    servers = [ORIGIN_DICT[n] for n in sorted(ORIGIN_DICT)]
    assert LEAN in ORIGIN_DICT, f"{LEAN} is not running; origins: {sorted(ORIGIN_DICT)}"
    print(f"origins: {[s.name for s in servers]}", file=sys.stderr)
    if args.mode == "seeds":
        run_seeds(servers, args.out)
    else:
        run_fuzz(servers, args.out, args.iterations, args.seed)


if __name__ == "__main__":
    main()
