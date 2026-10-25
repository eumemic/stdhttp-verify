#!/bin/sh
# Re-check Spec/Real/Framing.lean against the toolchain's own Std.Http instead of the patched
# copy in ../fix (the functions it is about are identical in both). Run from this directory after
# `lake build`.
set -eu
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
sed 's/^import HttpFix$/import Std.Http/' Spec/Real/Framing.lean > "$tmp/FramingShipped.lean"
cat >> "$tmp/FramingShipped.lean" <<'LEAN'

#print axioms HttpSpec.RealFraming.getSize_assigns
#print axioms HttpSpec.RealFraming.getSize_rejects
#print axioms HttpSpec.RealFraming.getSize_chunked_no_contentLength
LEAN
lake env lean "$tmp/FramingShipped.lean"
