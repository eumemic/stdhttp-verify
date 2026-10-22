"""Time how long each Garden origin takes to answer a body of N one-byte chunks (runs in the driver container)."""
import socket
import sys
import time

sys.path.insert(0, "/garden/tools")
from targets import ORIGIN_DICT  # noqa: E402
from util import ssl_wrap  # noqa: E402

n = int(sys.argv[1]) if len(sys.argv) > 1 else 40000
body = b"1\r\na\r\n" * n + b"0\r\n\r\n"
req = b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\nConnection: close\r\n\r\n" + body
for name in sorted(ORIGIN_DICT):
    srv = ORIGIN_DICT[name]
    sock = socket.create_connection((srv.address, srv.port))
    if srv.requires_tls:
        sock = ssl_wrap(sock, srv.address)
    sock.settimeout(60)
    t = time.time()
    sock.sendall(req)
    first = b""
    try:
        while True:
            b = sock.recv(1 << 16)
            if not b:
                break
            if not first:
                first = b
    except (TimeoutError, ConnectionResetError, OSError):
        pass
    print(f"{name:14s} {time.time() - t:7.3f}s  {first.split(b'\r\n')[0]!r}")
    sock.close()
