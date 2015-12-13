set -e # abort on error
source bin/lib.sh

for i in $(ls -1 ./preselect); do
  check "$i" ./preselect/$i
done
