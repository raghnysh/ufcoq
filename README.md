# Univalent Foundations in Coq

## Introduction

This project is an effort to formalise small parts of mathematics over
the [univalent foundations][1].  The formalisation is done in the
framework of the [Coq][2] proof assistant.  I have created the project
for my personal education.  You are welcome to explore it.

## Disclaimer

I am not an expert on the subject.  As I have mentioned above, this
project is for my personal education.  See the [UniMath][3] project
for the formalisation of a large body of mathematics over the
univalent foundations.

## Prerequisites

I will assume that anyone who wants to explore the project is

* familiar with the basics of Coq,
* working on a Unix-like operating system (Linux, FreeBSD, etc.), and
* knows how to run simple git commands.

## Setup

The project uses the [Nix][4] package manager, and the [direnv][5]
shell extension.  Install them using the instructions on their project
sites.  Then do

``` shell
git clone https://github.com/raghnysh/ufcoq
cd ufcoq
direnv allow
```

to set up the project.  The `direnv allow` step may take a while.  It
makes Nix download and install several required packages.  After its
completion, the project is ready to be built.

## Building

Building the project means compiling the Coq files in it.  After
setting up Nix and direnv as in the previous section, do

``` shell
make
```

in the top directory of the project.  A successful exit of this
command means that the project has been built properly.

## Copying

My name is Raghavendra Nyshadham.  I am the author of this work.  I
place it in the public domain through the Creative Commons CC0 1.0
Universal Public Domain Dedication.  I waive all copyright and related
rights to the work.  See the file ⟨[COPYING][6]⟩ for the CC0
dedication.  Alternatively, see
⟨[http://creativecommons.org/publicdomain/zero/1.0/][7]⟩.

[1]: https://en.wikipedia.org/wiki/Univalent_foundations
[2]: https://coq.inria.fr/
[3]: https://github.com/UniMath/UniMath
[4]: https://github.com/NixOS/nix
[5]: https://github.com/direnv/direnv
[6]: COPYING
[7]: http://creativecommons.org/publicdomain/zero/1.0/
