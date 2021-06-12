### Specification for nix-shell

let
  nixpkgsPath =
    builtins.fetchTarball {
      ## github:NixOS/nixpkgs, nixpkgs-unstable branch, 2021-05-12
      url = "https://github.com/NixOS/nixpkgs/archive/4d8dd0afd2d5a35acb5e34c5c7b1674b74173d87.tar.gz";
      sha256 = "1d7z53vzq9jjy0dmq8w952dlxvajxrbmbn9926yhfp610p93ns84";
    };
  ixnayPath = builtins.fetchTarball {
    ## github:nyraghu/ixnay, master branch, 2021-06-11
    url = "https://github.com/nyraghu/ixnay/archive/dc407795d7843b777c1700cc88753caa5c847087.tar.gz";
    sha256 = "01261rkg4savsn8wcl533psqk1aiwki57jviadgrfp31w0k8pvbm";
  };
  nixpkgs = import nixpkgsPath {};
  ixnay = import ixnayPath { inherit nixpkgs; };
  ## I am using `alectryon' for literate Coq.
  alectryon = ixnay.alectryon;
  python = alectryon.python;
  pythonEnvironment = python.withPackages (packages: [ alectryon ]);
  ## I am using `opam' to install `coq-serapi' on which `alectryon'
  ## depends.  There is no Nix expression for `coq-serapi' at present,
  ## see <https://github.com/ejgallego/coq-serapi/issues/241>.
  ##
  ## `gmp' is for some OCaml packages on which `coq-serapi' depends.
  packages = with nixpkgs; [ gmp opam ] ++ [ pythonEnvironment ];
  packagesManPath = nixpkgs.lib.makeSearchPath "share/man" packages;
  MANPATH = packagesManPath + ":" + (builtins.getEnv "MANPATH");
in nixpkgs.mkShell {
  buildInputs = packages;
  inherit MANPATH;
}

### End of file
