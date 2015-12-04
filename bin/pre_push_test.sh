set -e # abort on error

for i in $(ls -1 ./preselect); do
  ./preselect/$i
done
