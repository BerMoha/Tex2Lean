FROM leanprover/lean4:v4.33.0

USER root
WORKDIR /workspace

# Copie tous les fichiers de votre dépôt dans le conteneur
COPY . .

# Configuration d'un projet Lean 4 purement local (zéro téléchargement internet)
RUN cd authoring && \
    echo 'name = "drazin"' > lakefile.toml && \
    echo 'version = "0.1.0"' >> lakefile.toml && \
    echo 'default_target = "drazin"' >> lakefile.toml && \
    echo '[[lean_lib]]' >> lakefile.toml && \
    echo 'name = "Tex2lean"' >> lakefile.toml



