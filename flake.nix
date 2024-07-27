{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    haskell-flake.url = "github:srid/haskell-flake";
    ghc-wasm.url = "git+https://gitlab.haskell.org/ghc/ghc-wasm-meta"; #"https://gitlab.haskell.org/ghc/ghc-wasm-meta/-/archive/master/ghc-wasm-meta-master.tar.gz";
  };
  outputs = inputs@{ self, nixpkgs, flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = nixpkgs.lib.systems.flakeExposed;
      imports = [ inputs.haskell-flake.flakeModule];

      perSystem = { self', pkgs, config, ... }: 
        let f = set: builtins.trace "\n${builtins.concatStringsSep "\n" (builtins.attrNames set)}" set; in 
        {

        # Typically, you just want a single project named "default". But
        # multiple projects are also possible, each using different GHC version.
        haskellProjects.default = {
          # The base package set representing a specific GHC version.
          # By default, this is pkgs.haskellPackages.
          # You may also create your own. See https://community.flake.parts/haskell-flake/package-set
          #basePackages = pkgs.haskellPackages // inputs.ghc-wasm.packages;
          packages = {};
          settings = {};

          # Extra package information. See https://community.flake.parts/haskell-flake/dependency
          #
          # Note that local packages are automatically included in `packages`
          # (defined by `defaults.packages` option).
          #
          # packages = {
          #   aeson.source = "1.5.0.0"; # Hackage version override
          #   shower.source = inputs.shower;
          # };
          # settings = {
          #   aeson = {
          #     check = false;
          #   };
          #   relude = {
          #     haddock = false;
          #     broken = false;
          #   };
          # };

          # devShell = {
          #  # Enabled by default
          #  enable = true;
          #
          #  # Programs you want to make available in the shell.
          #  # Default programs can be disabled by setting to 'null'
          #  tools = hp: { fourmolu = hp.fourmolu; ghcid = null; };
          #
          #  hlsCheck.enable = true;
          # };

          devShell = {
            hlsCheck.enable = true;

           };
          autoWire = [ "packages" "apps" "checks" ];

        };

        # haskell-flake doesn't set the default package, but you can do it here.
        packages.default = self'.packages.ICFP2024;

        devShells.default = pkgs.mkShell {
          name = "haskell-template";
          meta.description = "Haskell development environment";
          # See https://community.flake.parts/haskell-flake/devshell#composing-devshells
          inputsFrom = [
            config.haskellProjects.default.outputs.devShell
          ];
          nativeBuildInputs = with (inputs.ghc-wasm.packages.${pkgs.system}); [wasmtime wasm32-wasi-ghc-9_6  wasm32-wasi-cabal-9_6 ]; #(f inputs.ghc-wasm.packages.x86_64-linux); [wasm32-wasi-ghc-9_6];
        };
      };
    };
}
