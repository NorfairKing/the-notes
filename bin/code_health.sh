set -e # Abort on error
./bin/trailing_whitespace_test.sh
./bin/indentation.sh
./bin/hlint_health.sh
./bin/line_length.sh
