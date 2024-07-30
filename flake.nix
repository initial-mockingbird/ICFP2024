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
        let 
          stack-wrapped = pkgs.symlinkJoin {
            name = "stack"; # will be available as the usual `stack` in terminal
            paths = [ pkgs.stack ];
            buildInputs = [ pkgs.makeWrapper ];
            postBuild = ''
              wrapProgram $out/bin/stack \
                --add-flags "\
                  --no-nix \
                  --system-ghc \
                  --no-install-ghc \
                "
            '';
          };
          unlit-wrapped = pkgs.symlinkJoin {
            name = "unlit"; # will be available as the usual `stack` in terminal
            paths = [ pkgs.haskellPackages.unlit ];
            buildInputs = [ pkgs.makeWrapper ];
          };
        in {

        # Typically, you just want a single project named "default". But
        # multiple projects are also possible, each using different GHC version.
        haskellProjects.default = {
          # The base package set representing a specific GHC version.
          # By default, this is pkgs.haskellPackages.
          # You may also create your own. See https://community.flake.parts/haskell-flake/package-set
          #basePackages = pkgs.haskellPackages // inputs.ghc-wasm.packages;
          basePackages = pkgs.haskell.packages.ghc982;
          packages = {
            #happy=pkgs.haskellPackages.happy;
            #alex=pkgs.haskellPackages.alex;
          };
          settings = {
             singletons-base = {
              check = false;
             };
             singletons-base_3_3 = {
              check = false;
             };
          };

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
            hoogle = true;

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
          nativeBuildInputs = 
            [ inputs.ghc-wasm.packages.${pkgs.system}.all_9_10
              stack-wrapped
              pkgs.hpack
              pkgs.just
            ];
        };
      };
    };
}
