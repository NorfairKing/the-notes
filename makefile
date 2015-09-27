NAME = notes

SRC_EXT = hs
TEX_EXT = tex
OUT_EXT = pdf
BIN_EXT = bin

BIN_NAME = $(NAME)
BIN = $(BIN_NAME).$(BIN_EXT)

SRC_DIR = src
MAIN_SRC_NAME = Main
MAIN_SRC = $(SRC_DIR)/$(MAIN_SRC_NAME).$(SRC_EXT)

OUTPUT_NAME = notes
OUTPUT = $(OUTPUT_NAME).$(OUT_EXT)

MAIN_NAME = main
MAIN_TEX = $(MAIN_NAME).$(TEX_EXT)
MAIN_OUT = $(MAIN_NAME).$(OUT_EXT)

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

LATEX = latexmk -pdf -pdflatex="pdflatex -shell-escape -halt-on-error -enable-write18"

all: pdf

bin: $(SOURCES)
	$(GHC) $(GHC_OPTIONS) -o $(BIN) --make $(MAIN_SRC)

tex: bin
	./$(BIN)

pdf: tex $(OUTPUT)

$(OUTPUT): $(MAIN_OUT)
	  cp $(MAIN_OUT) $(OUTPUT)

$(MAIN_OUT): $(MAIN_TEX)
	  $(LATEX) $(MAIN_TEX)

love:
	@echo "not war"
	
DIRTY_EXT = *.tex *.o *.hi *.bin

clean:
	rm -f $(BIN) $(DIRTY_EXT)
