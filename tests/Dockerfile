FROM leanprover/lean4:v4.33.0

USER root
WORKDIR /workspace

COPY . .

# Règle de structure obligatoire pour le bac à sable de test d'AfterQuery
COPY tests/test.sh /tests/test.sh
RUN chmod +x /tests/test.sh

RUN cd authoring && \
    echo 'name = "drazin"' > lakefile.toml && \
    echo 'version = "0.1.0"' >> lakefile.toml && \
    echo 'default_target = "drazin"' >> lakefile.toml && \
    echo '[[lean_lib]]' >> lakefile.toml && \
    echo 'name = "Tex2lean"' >> lakefile.toml

