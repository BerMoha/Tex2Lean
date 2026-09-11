#!/bin/bash
cd lean
if lake build Tex2lean.Model.Theorem | grep -q "error"; then
    echo "Validation failed"
    exit 1
else
    echo "Validation successful"
    exit 0
fi
