NAME = the-notes

SRC_EXT = hs

BIN = $(NAME)

SRC_DIR = src
MAIN_SRC_NAME = Main
MAIN_SRC = $(SRC_DIR)/$(MAIN_SRC_NAME).$(SRC_EXT)

SOURCES = $(wildcard $(SRC_DIR)/**/*.hs)

GHC = ghc
GHC_FLAGS = \
	-fwarn-unused-imports \
	-fwarn-incomplete-patterns \
	-Wall \
	-fno-warn-unused-do-bind \
	-fno-warn-name-shadowing \
	-XOverloadedStrings
GHC_SRC_DIRS = \
	-i$(SRC_DIR)
GHC_OPTIONS = \
	$(GHC_FLAGS) \
	$(GHC_SRC_DIRS)

bin: $(SOURCES)
	$(GHC) $(GHC_OPTIONS) -o $(BIN) --make $(MAIN_SRC)

love:
	@echo "not war"
	
DIRTY_EXT = *.tex *.o *.hi *.bin

clean:
	rm -f $(BIN) $(DIRTY_EXT)
