"""Segmentation test: does the server's interpretation change when the same bytes arrive split across TCP writes?

Usage: python3 -I harness/segment.py <garden_tools_dir> <host> <port> <out.jsonl>
"""
import json
import socket
import sys
from concurrent.futures import ThreadPoolExecutor

tools_dir, host, port = sys.argv[1], sys.argv[2], int(sys.argv[3])
out_path = sys.argv[4] if len(sys.argv) > 4 else "/dev/null"
sys.path.insert(0, tools_dir)
sys.path.insert(0, __import__("os").path.dirname(__file__))
from http1 import HTTPResponse, parse_response, parse_response_json  # noqa: E402
import seeds  # noqa: E402

TIMEOUT = 0.03


def recv_until_quiet(sock: socket.socket) -> bytes:
    data = b""
    while True:
        try:
            b = sock.recv(65536)
        except (TimeoutError, socket.timeout):
            break
        except ConnectionResetError:
            break
        if not b:
            break
        data += b
    return data


def roundtrip(pieces: list[bytes]) -> bytes:
    with socket.create_connection((host, port)) as s:
        s.settimeout(TIMEOUT)
        got = b""
        for p in pieces:
            try:
                s.sendall(p)
            except (BrokenPipeError, ConnectionResetError):
                break
            got += recv_until_quiet(s)
        got += recv_until_quiet(s)
        return got


def describe(raw: bytes) -> list[str]:
    out = []
    while raw:
        try:
            resp, raw = parse_response(raw)
        except ValueError:
            out.append(f"UNPARSEABLE {raw[:80]!r}")
            break
        if resp.code == b"200":
            try:
                r = parse_response_json(resp.body)
                out.append(f"ACCEPT {r.method!r} {r.uri!r} {sorted(r.headers)!r} body={r.body!r}")
            except ValueError:
                out.append(f"200-NONJSON {resp.body[:80]!r}")
        else:
            out.append(f"REJECT {resp.code.decode()}")
    return out


def check(item):
    name, payload, k = item
    split = describe(roundtrip([payload[:k], payload[k:]]))
    return name, k, split


def main() -> None:
    baselines = {name: describe(roundtrip([p])) for name, p in seeds.SEEDS.items()}
    # Re-run each baseline once more to catch nondeterminism.
    flaky = [n for n, p in seeds.SEEDS.items() if describe(roundtrip([p])) != baselines[n]]
    items = [(n, p, k) for n, p in seeds.SEEDS.items() if n not in flaky for k in range(1, len(p))]
    mismatches = []
    with ThreadPoolExecutor(12) as ex:
        for name, k, split in ex.map(check, items):
            if split != baselines[name]:
                mismatches.append({"seed": name, "split_at": k, "baseline": baselines[name], "split": split,
                                   "payload": repr(seeds.SEEDS[name]), "first": repr(seeds.SEEDS[name][:k])})
    with open(out_path, "w") as f:
        for m in mismatches:
            f.write(json.dumps(m) + "\n")
    print(f"{len(items)} split roundtrips, {len(flaky)} flaky baselines {flaky}, {len(mismatches)} mismatches")
    by_seed = {}
    for m in mismatches:
        by_seed.setdefault(m["seed"], []).append(m["split_at"])
    for s, ks in by_seed.items():
        print(f"  {s}: split positions {ks[:12]}{' ...' if len(ks) > 12 else ''} of {len(seeds.SEEDS[s])}")


if __name__ == "__main__":
    main()
