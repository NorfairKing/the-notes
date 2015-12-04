# The Notes

## Preselects

This is a large collection of notes.
Not all of them are coherent or related.
There are predefined selections of coherent subparts that can be compiled into a coherent collection of notes on a specific topic.
See the `preselect` directory.

## Raw Compilation

Compiling the notes generator is as easy as running `make`.
Generating the notes is done with `./the-notes`.

You can also generate subsets of the notes by adding selectors to the command.

- `./the-notes sets` will only generate the chapter on sets.
- `./the-notes sets.basics` will only generate the 'basics' section of the sets chapter
- `./the-notes sets probability` will only generate the chapters on sets and probability.


## Contribution
Contributions to these notes are very welcome in the form of pull requests or patches via email.

`IMPORTANT`, before contributing, please install the `bin/pre_commit_test.sh` hook into `.git/hooks/pre-commit`. You can do this by running `spark deploy hooks.sus` or by manually copying the file.

## Licence
"The Notes"
Copyright 2015 Tom Sydney Kerckhove

<a rel="license" href="http://creativecommons.org/licenses/by-nc/4.0/"><img alt="Creative Commons License" style="border-width:0" src="https://i.creativecommons.org/l/by-nc/4.0/88x31.png" /></a><br /><span xmlns:dct="http://purl.org/dc/terms/" href="http://purl.org/dc/dcmitype/Text" property="dct:title" rel="dct:type">The Notes</span> by <a xmlns:cc="http://creativecommons.org/ns#" href="http://cs-syd.eu" property="cc:attributionName" rel="cc:attributionURL">Tom Sydney Kerckhove</a> is licensed under a <a rel="license" href="http://creativecommons.org/licenses/by-nc/4.0/">Creative Commons Attribution-NonCommercial 4.0 International License</a>.<br />Based on a work at <a xmlns:dct="http://purl.org/dc/terms/" href="https://github.com/NorfairKing/the-notes" rel="dct:source">https://github.com/NorfairKing/the-notes</a>.
