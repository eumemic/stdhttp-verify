"""Minimal network repro: Std.Http answers 400 to a valid chunked request when it arrives in two TCP writes.

Usage: python3 split_400.py HOST PORT
"""
import socket
import sys
import time

host, port = sys.argv[1], int(sys.argv[2])
head = b"POST / HTTP/1.1\r\nHost: a\r\nTransfer-Encoding: chunked\r\n\r\n"
body = b"5;a=b\r\nhello\r\n0\r\n\r\n"


def send(pieces):
    with socket.create_connection((host, port)) as s:
        for p in pieces:
            s.sendall(p)
            time.sleep(0.1)
        s.settimeout(0.5)
        return s.recv(4096).split(b"\r\n")[0].decode()


print("one write          :", send([head + body]))
print("split after '5;'   :", send([head + body[:2], body[2:]]))
