echo "Checking for trailing whitespaces in code..."
TMP=/tmp/files.txt
find src -type f -name "*.hs" -exec egrep -l " +$" {} \; > $TMP
if [[ -s $TMP ]]
then
  code="1"
  echo "These files contain trailing whitespace, please fix: "
else
  code="0"
fi

while read f
do
  echo $f
done < $TMP

exit $code
