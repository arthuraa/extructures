{
  description = ''
    Finite sets, maps, and other data structures with extensional reasoning
  '';

  inputs.flake-utils.url = "github:numtide/flake-utils";

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages.${system};
          lib = pkgs.lib; in rec {
            packages = rec {
              coq = pkgs.coq_8_20;
              coqPackages = pkgs.coqPackages_8_20.overrideScope (self: super:
                { mathcomp = super.mathcomp.override {
                    version = "2.2.0";
                  };
                  deriving = super.deriving.overrideAttrs (s: {
                    version = "0.2.0";
                  });
                });
              ocaml = pkgs.ocaml;
            };

            devShell = pkgs.mkShell {
              packages = with packages; [
                coq
                coqPackages.mathcomp.ssreflect
                coqPackages.deriving
                ocaml
              ];
            };
      }
    );
}
