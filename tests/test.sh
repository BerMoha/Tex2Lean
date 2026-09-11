#!/bin/bash
mkdir -p /logs/verifier

# Default to failure
echo "0" > /logs/verifier/reward.txt

cd /tests
python3 -m pytest test_theorem.py --ctrf=/logs/verifier/ctrf-report.json -v && echo "1" > /logs/verifier/reward.txt

exit 0
