"""Compare two local servers' interpretation of each seed, sent in one write; with a fuzz count,
also of that many payloads mutated from the seeds by HTTP Garden's mutators.

Usage: python3 -I harness/compare.py <garden_tools_dir> <host> <port_a> <port_b> [fuzz_iterations]
"""
import random
import sys

tools_dir, host, port_a, port_b = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
iterations = int(sys.argv[5]) if len(sys.argv) > 5 else 0
sys.argv = [sys.argv[0], tools_dir, host, str(port_a)]
sys.path.insert(0, __import__("os").path.dirname(__file__))
import segment  # noqa: E402  (reads tools_dir, host and port from sys.argv)
import seeds  # noqa: E402
from mutations import mutate  # noqa: E402


def result(port: int, pieces: list[bytes]) -> list[str]:
    segment.port = port
    return segment.describe(segment.roundtrip([b"".join(pieces)]))


def compare(name: str, pieces: list[bytes]) -> bool:
    a, b = result(port_a, pieces), result(port_b, pieces)
    if a != b:
        print(f"{name}: {b''.join(pieces)!r}\n  {port_a}: {a}\n  {port_b}: {b}")
    return a == b


differ = sum(not compare(name, [p]) for name, p in seeds.SEEDS.items())
print(f"{len(seeds.SEEDS)} seeds, {differ} differ")

if iterations:
    random.seed(0)
    corpus = [[p] for p in seeds.SEEDS.values()]
    tried = differ = 0
    for i in range(iterations):
        payload = random.choice(corpus)
        try:
            for _ in range(random.randint(1, 3)):
                payload = mutate(payload)
        except (OverflowError, ValueError, RecursionError):
            continue  # the Garden's mutators can't parse some payloads (e.g. huge Content-Length)
        tried += 1
        differ += not compare(f"fuzz {i}", payload)
    print(f"{tried} mutated payloads, {differ} differ")
