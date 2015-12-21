source bin/lib.sh

line_length () {
  local RESULT_FILE="/tmp/line_length"
  for f in $(git diff --name-only) # $(find src -type f -name '*.hs')
  do
    grep --line-number '.\{80\}' "$f" > "$RESULT_FILE"
    if [[ "$?" == "0" ]]
    then
      print_colored_text RED $f
      echo
      cat "$RESULT_FILE"
      return -1
    fi
  done
}

check "Line Length Limit" line_length
