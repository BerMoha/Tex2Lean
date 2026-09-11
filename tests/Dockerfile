
FROM leanprover/lean4:v4.33.0

USER root
WORKDIR /workspace

COPY . .

RUN mkdir -p /tests && cp tests/test.sh /tests/test.sh && chmod +x /tests/test.sh

RUN cd authoring && \
    if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then \
        echo '[[dependency]]' > lakefile.toml && \
        echo 'name = "mathlib"' >> lakefile.toml && \
        echo 'git = "https://github.com"' >> lakefile.toml && \
        echo 'rev = "v4.33.0"' >> lakefile.toml; \
    fi && \
    lake update


