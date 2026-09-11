
FROM leanprover/lean4:v4.33.0
WORKDIR /workspace
COPY . .
RUN mkdir -p /tests
COPY tests/test.sh /tests/test.sh
RUN chmod +x /tests/test.sh
RUN cd authoring && lake build

