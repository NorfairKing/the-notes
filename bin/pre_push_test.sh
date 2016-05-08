set -e # abort on error

./bin/count_todos.sh
./bin/code_health.sh
./bin/build.sh
./bin/test.sh
./bin/install.sh
./bin/generate.sh
./bin/documentation.sh
./bin/all_preselects.sh
