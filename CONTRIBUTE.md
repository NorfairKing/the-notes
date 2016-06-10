# How to contribute

## Your first contribution

You do not even need to know Haskell to make a contribution.

- For the repository (Click the Fork button at the top right of this screen if you're reading this at github.com .)
- Clone your fork: `git clone https://github.com/YourUsername/the-notes`.
- Find a spelling error or some missing documentation for a function.
- Figure out where the code is that is involved.
- Fix it with your editor of choice.
- Add yourself to the list of contributors in `contributors.txt`.
- `git add src/Your/Changed/File/Here.hs contributors.txt`.
- `git commit -m "Spelling fix: Note instead of Nore`.
- Push the change to your fork: `git push`
- Make a pull request via the github UI.


## More extensive contributions

### Get the dependencies

To make more extensive contributions, you will need:

- `stack`
- `ghc`
- `cabal`
- `haddock`
- `hlint`
- `minted` (`pygmentize`)
- `latexmk`
- `dot`


### Install the git hooks

Before contributing, please install the `bin/pre_commit_test.sh` and `bin/pre_push_test.sh` hooks into `.git/hooks/pre-commit`. You can do this by running `spark deploy hooks.sus` or by manually copying the files.


### Continuous builds

You can have `stack` rebuild the notes while you change them with the following command.

```
stack install --exec=the-notes --file-watch
```

Open up a terminal and keep it running while you change the code.
Keep a pdf reader open on the file `out/the-notes.pdf`
Every time you save a change, `stack` will rebuild the generator and run it again, so you can see your change.


### Documentation

There are *a lot* of functions in this project.
Some of them, especially commonly used ones, are documented.
You can build the documentation with `make doc` but it will take a while.
