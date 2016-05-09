source bin/lib.sh
h () {
  hlint src \
  --ignore "Redundant do" \
  --ignore "Redundant $" \
  --ignore "Redundant bracket"  \
  --ignore "Parse error"  \
  --ignore "Reduce duplication"  \
  --ignore "Use camelCase"  \
  --ignore "Use import/export shortcut"  \
  --ignore "Use ." \
  --ignore "Move brackets to avoid $" \
  --ignore "Evaluate" \
  --ignore "Use 1" \
  -XFlexibleInstances \
  -XMultiParamTypeClasses \
  -XUndecidableInstances \
  -XQuasiQuotes \
  -XTemplateHaskell
}
check "Hlint" h
