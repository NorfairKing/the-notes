source bin/lib.sh

pedantic () {
  stack clean
  stack build \
    --pedantic \
    --fast \
    --jobs=8 \
    --ghc-options="\
      -fforce-recomp \
      -O0
      -Wall
      -Werror
      -fwarn-unused-imports \
      -fwarn-incomplete-patterns \
      -fwarn-unused-do-bind \
      -fno-warn-name-shadowing \
      -fno-warn-orphans"
}
check "Pedantic checking" pedantic
