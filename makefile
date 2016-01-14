NAME = the-notes

SRC_EXT = hs

BIN = $(NAME)

SRC_DIR = src
MAIN_SRC_NAME = Main
MAIN_SRC = $(SRC_DIR)/$(MAIN_SRC_NAME).$(SRC_EXT)

SOURCES = $(shell find $(SRC_DIR) -type f -name '*.hs')

GHC = ghc
GHC_FLAGS = \
	-j8 \
	-XOverloadedStrings \
	-XNoImplicitPrelude \
	-XTemplateHaskell

GHC_SRC_DIRS = \
	-i$(SRC_DIR)
GHC_OPTIONS = \
	$(GHC_FLAGS) \
	$(GHC_SRC_DIRS)

all: bin
	./the-notes --tmp-dir out
	./bin/all_preselects.sh

bin: $(SOURCES)
	$(GHC) $(GHC_OPTIONS) -o $(BIN) --make $(MAIN_SRC)

WARNINGS = \
	-Wall -Werror \
	-fwarn-unused-imports \
	-fwarn-incomplete-patterns \
	-fwarn-unused-do-bind \
	-fno-warn-name-shadowing \
	-fno-warn-orphans \

pedantic:
	$(GHC) $(GHC_OPTIONS) $(WARNINGS) -fforce-recomp -o $(BIN) --make $(MAIN_SRC)

doc: $(SOURCES)
	cabal haddock --executables --haddock-options="--no-warnings --no-print-missing-docs --pretty-html"

graph:
	graphmod $(MAIN_SRC) -q -p -i $(SRC_DIR) > graph.dot

love:
	@echo "not war"
	
DIRTY_EXT = *.tex *.o *.hi *.bin

clean:
	rm -f $(BIN) $(DIRTY_EXT)
