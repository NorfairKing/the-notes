set -e # abort on error

./bin/pre_commit_test.sh
./bin/documentation.sh

echo "Trying out all preselections..."
for i in $(ls -1 ./preselect); do
  ./preselect/$i
done
