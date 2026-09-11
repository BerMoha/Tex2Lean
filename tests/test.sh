#!/bin/bash
mkdir -p /logs/verifier
cd /workspace/authoring

# Execute lake build and check for compile validation
if lake build Tex2lean.Model.Theorem 2>&1 | grep -q "error"; then
    echo "Validation failed"
    echo "0" > /logs/verifier/reward.txt
    exit 1
else
    echo "Validation successful"
    echo "1" > /logs/verifier/reward.txt
    exit 0
fi


