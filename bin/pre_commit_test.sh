#!/bin/bash

# Abort on error
set -e

echo "Testing whether you're allowed to do this."
echo

./bin/code_health.sh
./bin/build.sh
./bin/generate.sh

echo "All clear!"
