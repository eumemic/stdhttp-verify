"""Send each seed one byte per TCP write and compare with the single-write result.

Usage: python3 -I harness/bytewise.py <garden_tools_dir> <host> <port>
"""
import os
import sys
from concurrent.futures import ThreadPoolExecutor

sys.path.insert(0, os.path.dirname(__file__))
import segment  # noqa: E402
import seeds  # noqa: E402


def run(item):
    name, payload = item
    base = segment.describe(segment.roundtrip([payload]))
    byte = segment.describe(segment.roundtrip([payload[i:i + 1] for i in range(len(payload))]))
    return name, base, byte


with ThreadPoolExecutor(16) as ex:
    results = list(ex.map(run, seeds.SEEDS.items()))
kinds = {}
for name, base, byte in results:
    if base != byte:
        kind = f"{'ACCEPT' if any(b.startswith('ACCEPT') for b in base) else 'REJECT'} -> " \
               f"{'ACCEPT' if any(b.startswith('ACCEPT') for b in byte) else 'REJECT'}"
        kinds.setdefault(kind, []).append(name)
        print(f"{name:28s} single={base}\n{'':28s} bytewise={byte}")
print({k: len(v) for k, v in kinds.items()})
