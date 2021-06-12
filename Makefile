### Makefile for the project

### ==================================================================
### Variables
### ==================================================================

## The default target of the project
.DEFAULT_GOAL = all

## File whose presence indicates that nix-build has been run
NIXBUILD_COOKIE = .nixbuild_done

## The name of the symbolic link created by nix-build.
NIXBUILD_LINK = .nix

### ==================================================================
### Rules
### ==================================================================

## The default target
.PHONY: all

## Target for running nix-build
.PHONY all: nixbuild

nixbuild: ${NIXBUILD_COOKIE}

${NIXBUILD_COOKIE}: default.nix misc/nix/*.nix
	nix-build --out-link ${NIXBUILD_LINK}
	touch $@

## Target for cleaning the dune output
.PHONY: clean

clean:
	@true
	# ${RM} -r ${BUILD_DIRECTORY}

## Target for cleaning the latexmk and nix-build outputs
.PHONY: distclean

distclean: clean
	${RM} ${NIXBUILD_COOKIE} ${NIXBUILD_LINK}

### End of file
