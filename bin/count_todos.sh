source bin/lib.sh

count_todos () {
  MAX_TODOS="500"
  TMP_FILE="/tmp/out.txt"
  rm -f "${TMP_FILE}"

  TODO_KEYWORDS=(
    "TODO"
    "FIXME"
    "todo"
    "todo_"
    "why"
    "why_"
    "toprove"
    )


  total="0"

  for todo in ${TODO_KEYWORDS[@]}
  do
    keywordtext="$(printf "%-10s" "${todo}:")"
    print_colored_text BLUE "${keywordtext}"

    local cmd="grep --color=auto --word-regexp "${todo}" --recursive --exclude Todo.hs src"
    ${cmd} >> "${TMP_FILE}"
    num="$($cmd | wc -l)"
    text="$(printf "%5d" "${num}")"

    if [ "${num}" == "0" ] ; then
      print_colored_text GREEN "${text}\n"
    elif [ ${num} -le $((MAX_TODOS / 2)) ] ; then
      print_colored_text YELLOW "${text}\n"
    else
      print_colored_text RED "${text} WARNING\n"
    fi

    total="$((${total} + ${num}))"
  done

  echo

  print_colored_text BLUE "$(printf "%-10s" "total:")"
  text="$(printf "%5d" "${total}")"
  if [ "$total" == "0" ] ; then
    print_colored_text GREEN "${text}\n"
  elif [ ${total} -le ${MAX_TODOS} ] ; then
    print_colored_text YELLOW "${text}\n"
  else                           
    cat "${TMP_FILE}" | sort
    print_colored_text RED "${text}\n"
    
    echo "I cannot let you go through with this. Fix some todo's first!"
    return -1
  fi  
}

printf "Check: Making sure there aren't too many todo's left in the code\n"
count_todos
if [[ "$?" == "0" ]]
then
  print_colored_text GREEN "Success\n"
else
  exit -1
fi
