{
  description = "Functions and sets with extensional reasoning";

  inputs = {
    flake-parts.url = "github:hercules-ci/flake-parts";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    nix-github-actions.url = "github:nix-community/nix-github-actions";
    nix-github-actions.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs@{ self, flake-parts, nixpkgs, nix-github-actions, ... }:
    let
      coqVersions = [
        "9_2"
        "9_1"
        "9_0"
        "8_20"
        "8_19"
        "8_18"
        "8_17"
      ];
      defaultVersion = builtins.head coqVersions;
    in
    flake-parts.lib.mkFlake { inherit inputs; } {
      imports = [
        # To import a flake module
        # 1. Add foo to inputs
        # 2. Add foo as a parameter to the outputs function
        # 3. Add here: foo.flakeModule

      ];
      systems = [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" "x86_64-darwin" ];
      perSystem = { config, self', inputs', pkgs, system, ... }: {
        # Per-system attributes can be defined here. The self' and inputs'
        # module parameters provide easy access to attributes of the same
        # system.

        _module.args.pkgs = import self.inputs.nixpkgs {
          inherit system;
          overlays = [
            self.overlays.default
          ];
          config = { };
        };

        devShells.default = pkgs.mkShell {
          propagatedBuildInputs = [
            pkgs.coqPackages.coq-lsp
          ];
          inputsFrom = [
            self'.packages.default
          ];
        };

        # Equivalent to  inputs'.nixpkgs.legacyPackages.hello;
        packages =
          let packagesByVersion =
                nixpkgs.lib.listToAttrs
                  (map (coqVersion: {
                    name = coqVersion;
                    value = pkgs."coqPackages_${coqVersion}".extructures;
                  }) coqVersions);
          in
            packagesByVersion // {
              default = packagesByVersion.${defaultVersion};
            };

        checks = builtins.mapAttrs (set: package:
          package.overrideAttrs { doCheck = true; })
          self'.packages;

      };
      flake = {
        # The usual flake attributes can be defined here, including system-
        # agnostic ones like nixosModule and system-enumerating ones, although
        # those are more easily expressed in perSystem.

        githubActions = nix-github-actions.lib.mkGithubMatrix {
          checks =
            # Drop the "default" check — it is an alias for one of
            # the versioned checks, and including it would build
            # the same derivation twice in CI.
            builtins.mapAttrs
              (_: checks: builtins.removeAttrs checks [ "default" ])
              (nixpkgs.lib.getAttrs
                [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ]
                self.checks);
        };

        overlays.default = final: prev:
          let
            overrideLibraryDerivation = f: drv:
              drv.override (args:
                if args ? mkRocqDerivation then {
                  mkRocqDerivation = a:
                    (args.mkRocqDerivation a).override f;
                } else {
                  mkCoqDerivation = a:
                    (args.mkCoqDerivation a).override f;
                });

            overrideExtructures = coqPackages:
              coqPackages.overrideScope (final': prev': {
                extructures = overrideLibraryDerivation {
                  version = ./.;
                } prev'.extructures;
              });
          in
            nixpkgs.lib.listToAttrs
              (map (coqVersion:
                { name = "coqPackages_${coqVersion}";
                  value = overrideExtructures prev."coqPackages_${coqVersion}";})
                coqVersions);
      };
    };
}
