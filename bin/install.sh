source bin/lib.sh
install () {
  stack install
}
check "Install" install
