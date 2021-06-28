### Makefile for the project

### ==================================================================
### Variables
### ==================================================================

## The default target of the project
.DEFAULT_GOAL = all

## The main documentation file
TOC_FILE = _build/default/doc/html/toc.html

## OPAM files generated by dune
OPAM_FILES = ufcoq.opam ufcoq-doc.opam

## File whose presence indicates that nix-build has been run
NIXBUILD_COOKIE = .nixbuild_done

## The name of the symbolic link created by nix-build
NIXBUILD_LINK = .nix

## Fragments database (recutils)
FRAGMENTS_DATABASE = misc/fragments/fragments.rec

## Program to generate the above database
FRAGMENTS_PROGRAM = misc/fragments/fragments.awk

## The root of the physical paths of the Coq modules of the project.
COQ_ROOT = src

## The physical paths of the Coq modules of the project.
COQ_FILES = $(shell find ${COQ_ROOT} -name '*.v')

## If the variable VERBOSE has a blank value, execute recipes silently
## without printing them.
ifeq ($(strip ${VERBOSE}),)
MAKEFLAGS += --silent
endif

## The default target
.DEFAULT_GOAL = all

### ==================================================================
### Rules
### ==================================================================

## The default target
.PHONY: all

all:
	dune build --display=short @install
	if command -v xclip > /dev/null 2>&1; then \
		realpath ${TOC_FILE} | xclip -r -sel clip ; \
	fi

## Target for running nix-build
.PHONY: nixbuild

nixbuild: ${NIXBUILD_COOKIE}

${NIXBUILD_COOKIE}: default.nix misc/nix/*.nix
	nix-build --out-link ${NIXBUILD_LINK}
	touch $@

## Target for generating the fragments database
.PHONY: fragments-database
fragments-database: ${FRAGMENTS_DATABASE}

${FRAGMENTS_DATABASE}: ${COQ_FILES}
	awk -f ${FRAGMENTS_PROGRAM} $^ > $@

## Target for cleaning the dune output
.PHONY: clean

clean:
	dune clean
	${RM} ${OPAM_FILES} ${FRAGMENTS_DATABASE}

## Target for cleaning the dune and nix-build outputs
.PHONY: distclean

distclean: clean
	${RM} ${NIXBUILD_COOKIE} ${NIXBUILD_LINK}

### End of file
