source bin/lib.sh

partname="${*}"
if [[ "${partname}" == "" ]]
then
  echo "supply the part's module name as an argument"
  exit -1
fi

tofile () {
  file=$(echo "${1}" | sed -e 's/\./\//g')
  echo "src/${file}.hs"
}

dirof () {
  local part="$(tofile "${1}")"
  dirname "${part}"
}

echo $partname
echo $partfile
echo $partdir

create_main () {
  local part="${partname}"
  local dir="$(dirof "${part}")"
  local file="$(tofile "${part}")"
  local partfile="$(tofile "${part}")"

  mkdir -p "${dir}"

  read -r -d '' str <<- EOF
module ${part} where

import Notes

-- import ${partname}.Macro
-- import ${partname}.Terms
EOF
  echo "${str}" > "${partfile}"
}

create_terms () {
  local part="${partname}.Terms"
  local dir="$(dirof "${part}")"
  local file="$(tofile "${part}")"
  local partfile="$(tofile "${part}")"

  mkdir -p "${dir}"

  read -r -d '' str <<- EOF
module ${part} where

import Notes

EOF
  echo "${str}" > "${partfile}"
}

create_macro () {
  local part="${partname}.Macro"
  local dir="$(dirof "${part}")"
  local file="$(tofile "${part}")"
  local partfile="$(tofile "${part}")"

  mkdir -p "${dir}"

  read -r -d '' str <<- EOF
module ${part} where

import Types

EOF
  echo "${str}" > "${partfile}"
}

create_main
create_terms
create_macro
