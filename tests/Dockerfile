FROM ubuntu:22.04
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends git curl ca-certificates python3 python3-pip && rm -rf /var/lib/apt/lists/*
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"
RUN pip3 install --break-system-packages pytest==8.4.1 pytest-json-ctrf==0.3.5 || pip3 install pytest==8.4.1 pytest-json-ctrf==0.3.5
WORKDIR /workspace/authoring
COPY tests/lakefile.lean tests/lean-toolchain tests/Tex2lean.lean ./
RUN mkdir -p /workspace/authoring/Tex2lean/Model /workspace/authoring/Tex2lean/Analysis /workspace/authoring/Tex2lean/Meta
RUN lake update
RUN lake exe cache get || true
COPY tests/Checker.lean /workspace/authoring/Tex2lean/Checker.lean
COPY tests/ /tests/
RUN mkdir -p /app /logs/verifier
