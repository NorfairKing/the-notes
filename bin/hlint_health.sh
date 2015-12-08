echo "Running hlint..."
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
  --ignore "Warning: Move brackets to avoid $" \
  -XFlexibleInstances \
  -XMultiParamTypeClasses \
  -XUndecidableInstances \
  -XQuasiQuotes \
  -XTemplateHaskell

