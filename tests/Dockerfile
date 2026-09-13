FROM leanprover/lean4:v4.33.0
RUN apt-get update && apt-get install -y --no-install-recommends git curl python3 python3-pip && rm -rf /var/lib/apt/lists/*
RUN pip3 install --break-system-packages pytest==8.4.1 pytest-json-ctrf==0.3.5 || pip3 install pytest==8.4.1 pytest-json-ctrf==0.3.5
WORKDIR /workspace/authoring
COPY lakefile.lean lean-toolchain Tex2lean.lean ./
RUN mkdir -p /workspace/authoring/Tex2lean/Model /workspace/authoring/Tex2lean/Analysis /workspace/authoring/Tex2lean/Meta
RUN lake update
RUN lake exe cache get || true
RUN lake build
COPY Checker.lean /workspace/authoring/Tex2lean/Checker.lean
COPY . /tests/
RUN mkdir -p /app /logs/verifier
