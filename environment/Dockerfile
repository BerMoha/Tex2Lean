FROM leanprover/lean4:v4.33.0

USER root
WORKDIR /workspace

# Copy everything into the isolated evaluation container
COPY . .

# Navigate dynamically to the authoring folder and initialize the Lean configuration
RUN cd authoring && \
    if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then \
        echo '[[dependency]]' > lakefile.toml && \
        echo 'name = "mathlib"' >> lakefile.toml && \
        echo 'git = "https://github.com"' >> lakefile.toml && \
        echo 'rev = "v4.33.0"' >> lakefile.toml; \
    fi && \
    lake update

# Pre-compile the theorem to cache dependencies inside the image
RUN cd authoring && lake build Tex2lean.Model.Theorem || true


