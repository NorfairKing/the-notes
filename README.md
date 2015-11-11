# The Notes

## Compilation

Compiling the notes generator is as easy as running `make`.
Generating the notes is done with `./the-notes`.

You can also generate subsets of the notes by adding selectors to the command.

- `./the-notes sets` will only generate the chapter on sets.
- `./the-notes sets.basics` will only generate the 'basics' section of the sets chapter
- `./the-notes sets probability` will only generate the chapters on sets and probability.


## Contribution
Contributions to these notes are very welcome in the form of pull requests or patches via email.

IMPORTANT, before contributing, please install the `bin/pre_commit_test.sh` hook into `.git/hooks/pre-commit`. You can do this by running `[spark](https://github.com/NorfairKing/super-user-spark) deploy hooks.sus` or by manually copying the file.

## Licence

"The Notes"
Copyright 2015 Tom Sydney Kerckhove

This publication is free; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation.

This publication is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License (in the `LICENCE` file) for more details.

