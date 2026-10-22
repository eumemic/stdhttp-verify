FROM http-garden-soil:latest

# The soil image exports sanitizer CFLAGS/LDFLAGS for C targets; Lean builds with its own toolchain.
ENV CFLAGS='' CXXFLAGS='' LDFLAGS=''

RUN apt -y update \
 && apt -y install --no-install-recommends curl \
 && rm -rf /var/lib/apt/lists/*

ARG LEAN_TOOLCHAIN=leanprover/lean4:nightly-2026-10-20
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain "$LEAN_TOOLCHAIN"
ENV PATH="/root/.elan/bin:$PATH"

WORKDIR /app/echo
COPY lakefile.toml Main.lean ./
RUN echo "$LEAN_TOOLCHAIN" > lean-toolchain && lake build

CMD ["/app/echo/.lake/build/bin/echo", "80"]
