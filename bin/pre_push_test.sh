set -e # abort on error

./bin/code_health.sh
./bin/build.sh
./bin/generate.sh
./bin/install.sh
./bin/documentation.sh
./bin/all_preselects.sh
