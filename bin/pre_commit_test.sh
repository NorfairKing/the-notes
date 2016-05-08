#!/bin/bash

# Abort on error
set -e

./bin/code_health.sh
./bin/build.sh
./bin/test.sh
./bin/install.sh
./bin/generate.sh
