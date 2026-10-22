#!/bin/bash
# Usage: run_driver.sh <driver args...>  (runs the driver on the Garden network)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
exec docker run --rm --network http-garden_default --label com.docker.compose.service=garden-driver \
  -v /var/run/docker.sock:/var/run/docker.sock \
  -v "$ROOT/vendor/http-garden:/garden:ro" \
  -v "$ROOT/harness:/harness:ro" \
  -v "$ROOT/out:/out" \
  garden-driver python3 -u /harness/driver.py "$@"
