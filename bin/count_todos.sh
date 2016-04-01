source bin/lib.sh

count_todos () {
  MAX_TODOS="100"

  TODO_KEYWORDS=(
    "TODO"
    "FIXME"
    "todo"
    "todo_"
    "why"
    "why_"
    )


  total="0"

  for todo in ${TODO_KEYWORDS[@]}
  do
    keywordtext="$(printf "%-10s" "${todo}:")"
    print_colored_text BLUE "${keywordtext}"
    num="$(grep --color=auto --word-regexp "${todo}" --recursive --exclude 'Todo.hs' src | wc -l)"
    text="$(printf "%5d" "${num}")"

    if [ "${num}" == "0" ] ; then
      print_colored_text GREEN "${text}"
    elif [ ${num} -le $((MAX_TODOS / 2)) ] ; then
      print_colored_text YELLOW "${text}"
    else
      print_colored_text RED "${text} WARNING"
    fi
    printf "\n"

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
    print_colored_text RED "${text}\n"
    
    echo "I cannot let you go through with this. Fix some todo's first!"
    return -1
  fi  
}

check "Counting todo's" count_todos
