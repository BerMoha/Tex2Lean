FROM leanprover/lean4:v4.33.0
RUN apt-get update && apt-get install -y --no-install-recommends git curl && rm -rf /var/lib/apt/lists/*
WORKDIR /workspace/authoring
COPY lakefile.lean lean-toolchain Tex2lean.lean ./
RUN mkdir -p Tex2lean/Model
RUN lake update
RUN lake exe cache get || true
RUN lake build
