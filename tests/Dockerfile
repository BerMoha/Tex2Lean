FROM leanprover/lean4:v4.33.0
WORKDIR /workspace
COPY . .
RUN mkdir -p /tests && COPY tests/ /tests/
RUN cd authoring && lake build

