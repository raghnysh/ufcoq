# Univalent Foundations in Coq

## Introduction

This project is an effort to formalise small parts of mathematics over
the [univalent foundations][1] in the framework of the [Coq][2] proof
assistant.  I have created the project mainly for my personal
education, but you are welcome to explore it.

## Disclaimer

I am not an expert on the subject, and, as I have mentioned above,
this project is for my personal education.  Please visit the [UniMath
project site][3] to see the formalisation of a large body of
mathematics over the univalent foundations.

## Prerequisites

If you want to explore this project, please note that I will assume
that you are

* familiar with the basics of Coq,
* working on a Unix-like operating system (Linux, macOS, etc.), and
* know how to run simple git commands.

## Setup

The project uses the [Nix][4] package manager, and the [direnv][5]
shell extension.  Install them using the instructions on their project
sites, and then do

``` shell
git clone https://github.com/nyraghu/ufcoq
cd ufcoq
direnv allow
```

to set up the project.  The `direnv allow` step may take a while
because it makes Nix download and install several required packages.
After its completion, the project is ready to be built.

## Building

Building the project means compiling the Coq files in it.  As the
project uses Nix and direnv, it can be built in any environment that
is supported by these two tools.  This amounts to bash, or one of a
few other shells, running on a Unix-like operating system.

After setting up Nix and direnv as in the previous section, do

``` shell
make
```

in the top directory of the project (the one containing the file
`shell.nix`).  A successful exit of the `make` command indicates that
the Coq files in the project have been compiled properly.

[1]: https://en.wikipedia.org/wiki/Univalent_foundations
[2]: https://coq.inria.fr/
[3]: https://github.com/UniMath/UniMath
[4]: https://github.com/NixOS/nix
[5]: https://github.com/direnv/direnv
