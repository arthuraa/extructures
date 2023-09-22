{
  description = ''
    Finite sets, maps, and other data structures with extensional reasoning
  '';

  inputs.flake-utils.url = "github:numtide/flake-utils";

  inputs.deriving.url = "github:arthuraa/deriving/mathcomp-2.0.0";
  inputs.deriving.inputs.nixpkgs.follows = "nixpkgs";
  inputs.deriving.inputs.flake-utils.follows = "flake-utils";

  outputs = { self, nixpkgs, flake-utils, deriving }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
          derivingSrc = deriving;
          lib = pkgs.lib; in rec {
            packages = rec {
              coq = pkgs.coq_8_17;
              coqPackages = pkgs.coqPackages_8_17.overrideScope' (self: super:
                { mathcomp = super.mathcomp.override {
                    version = "2.0.0";
                  };
                  deriving = super.deriving.overrideAttrs (s: {
                    version = "dev";
                    src = derivingSrc;
                  });
                });
              ocaml = pkgs.ocaml;
            };

            devShell = pkgs.mkShell {
              packages = with packages; [ coq coqPackages.mathcomp.ssreflect coqPackages.deriving ocaml ];
            };
      }
    );
}
