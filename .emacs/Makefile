### Makefile for tasks related to Emacs in the project

### ==================================================================
### Variables
### ==================================================================

## The tags table.
TAGS_FILE = TAGS

## The root of the physical paths of the Coq modules of the project.
COQ_ROOT = ../src

## The physical paths of the Coq modules of the project.
COQ_FILES = $(shell find ${COQ_ROOT} -name '*.v')

## The file containing the regular expressions that match the
## identifiers being tagged.
REGEX_FILE = etags-regex

## The etags command.
ETAGS = etags --language=none --regex=@${REGEX_FILE}

## Test file containing dummy source code for testing the above
## regular expressions file.
REGEX_TEST_FILE = etags-regex.v

## Tags table for the above test file.
REGEX_TEST_TAGS = etags-regex.tags

## Golden tags table for the above test file.
REGEX_TEST_GOLD = etags-regex.gold

## If the variable VERBOSE has a blank value, execute recipes silently
## without printing them.
ifeq ($(strip ${VERBOSE}),)
MAKEFLAGS += --silent
endif

## The default target.
.DEFAULT_GOAL = all

### ==================================================================
### Targets
### ==================================================================

.PHONY: all
all: tags

.PHONY: tags
tags: ${TAGS_FILE}

${TAGS_FILE}: ${COQ_FILES} ${REGEX_FILE}
	${ETAGS} ${COQ_FILES}

.PHONY: tags-gold
tags-gold: ${REGEX_TEST_GOLD}

${REGEX_TEST_GOLD}: ${REGEX_TEST_FILE} ${REGEX_FILE}
	${ETAGS} --output=$@ $<

.PHONY: tags-test
tags-test:
	${ETAGS} --output=${REGEX_TEST_TAGS} ${REGEX_TEST_FILE}
	diff ${REGEX_TEST_GOLD} ${REGEX_TEST_TAGS}

.PHONY: clean
clean:
	${RM} ${TAGS_FILE} ${REGEX_TEST_TAGS}

### End of file
