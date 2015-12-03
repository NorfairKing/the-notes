#!/bin/bash

# Abort on error
set -e

# Make sure code quality is up to par
hlint src \
  --ignore "Redundant do" \
  --ignore "Redundant $" \
  --ignore "Redundant bracket"  \
  --ignore "Parse error"  \
  --ignore "Reduce duplication"  \
  --ignore "Use camelCase"  \
  --ignore "Use import/export shortcut"  \
  --ignore "Use ." \
  -XFlexibleInstances \
  -XMultiParamTypeClasses \
  -XUndecidableInstances \
  -XQuasiQuotes \
  -XTemplateHaskell

# Make sure the build succeeds
make

# Make sure compilation of the pdf succeeds
./the-notes
