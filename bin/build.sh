source bin/lib.sh
build () {
  stack build --jobs=8
}
check "Build" build
