set -e # abort on error

./bin/pre_commit_test.sh
for i in $(ls -1 ./preselect); do
  ./preselect/$i
done
