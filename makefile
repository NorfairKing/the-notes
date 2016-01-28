SOURCES = $(shell find $(SRC_DIR) -type f -name '*.hs')

all: bin
	the-notes
	./bin/all_preselects.sh

build: $(SOURCES)
	stack build --jobs=8

pedantic:
	stack clean
	stack build \
		--pedantic \
		--fast \
		--jobs=8 \
		--ghc-options="\
				-fforce-recomp \
				-O0 \
				-Wall \
				-Werror \
				-fwarn-unused-imports \
				-fwarn-incomplete-patterns \
				-fwarn-unused-do-bind \
				-fno-warn-name-shadowing \
				-fno-warn-orphans"

doc: $(SOURCES)
	cabal haddock \
		--executables \
		--haddock-options="--no-warnings --no-print-missing-docs --pretty-html"

test:
	stack test --jobs=8

install:
	stack install

fast:
	stack install \
		--fast \
		--jobs=8 \
		--ghc-options="\
				-O0 \
				"

love:
	@echo "not war"
	
DIRTY_EXT = *.tex *.o *.hi *.bin

clean:
	rm -f $(BIN) $(DIRTY_EXT)
