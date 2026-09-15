FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends git curl ca-certificates && rm -rf /var/lib/apt/lists/*
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"
WORKDIR /workspace/authoring
COPY environment/lakefile.lean environment/lean-toolchain environment/Tex2lean.lean ./
RUN mkdir -p /workspace/authoring/Tex2lean/Model /workspace/authoring/Tex2lean/Analysis /workspace/authoring/Tex2lean/Meta
RUN lake update
RUN lake exe cache get || true
RUN lake build
