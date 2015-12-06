set -e # abort on error

./bin/pre_commit_test.sh

make doc

for i in $(ls -1 ./preselect); do
  ./preselect/$i
done
