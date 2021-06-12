### Nix expression for the environment for the project

let
  nixpkgsPath = builtins.fetchTarball {
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
  generalPackages = with nixpkgs; [
    ## I am using `opam' to install `coq-serapi' on which `alectryon'
    ## depends.  There is no Nix expression for `coq-serapi' at
    ## present <https://github.com/ejgallego/coq-serapi/issues/241>.
    opam

    ## For some OCaml packages on which `coq-serapi' depends.
    gmp
  ];
  packages = [ pythonEnvironment ] ++ generalPackages;
in {
  inherit (nixpkgs) buildEnv mkShell;
  inherit packages;
}

### End of file
