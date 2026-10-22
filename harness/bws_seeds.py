import sys
sys.path.insert(0, "/harness"); sys.path.insert(0, "/garden/tools")
from fanout import fanout
from targets import ORIGIN_DICT
from driver import describe
servers = [ORIGIN_DICT[n] for n in sorted(ORIGIN_DICT)]
head = b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
for line in [b"5;a \r\n", b"5;a\t\r\n"]:
    res = fanout([head + line + b"hello\r\n0\r\n\r\n"], servers)
    print(repr(line), {s.name: (describe(r[0])[:22] if r else "-") for s, r in zip(servers, res)})
