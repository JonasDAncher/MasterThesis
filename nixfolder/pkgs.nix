let
  pkgs = import ./pin.nix { };
  coqPackages = pkgs.coqPackages.overrideScope' (cfinal: cprev: {
      coq = cprev.coq.override { version = "8.16.1"; };
      mathcomp = cprev.mathcomp.override { version = "1.15.0"; };
      mathcomp-analysis = cprev.mathcomp-analysis.override { version = "0.5.3"; };
      
      # Trying to add hacspec dependencies to the environment
      # compcert = cprev.compcert.override { version = "3.13.1"; };
      # coqprime = cprev.coqprime.override { version = "8.18"; };
      # QuickChick = cprev.QuickChick.override { version = "v2.0.2"; };
  });
  coqDeps = with coqPackages;
    [ deriving equations extructures mathcomp.ssreflect mathcomp-analysis compcert coqprime QuickChick pkgs.rust-bindgen pkgs.jasmin.xseq ];
  ssprove = coqPackages.callPackage ( { coq, stdenv, fetchFromGitHub }:
    stdenv.mkDerivation {
      name = "coq${coq.coq-version}-ssprove";

      src = fetchFromGitHub {
        owner = "SSProve";
        repo = "ssprove";
        rev = "e903a2a85634889121b70e27b7a4503a7e64b10a";
        sha256 = "E8Xt7SQWveJGC1ELC/BrgcWcspyIGIs6ICwullIt7uw=";
      };

      propagatedBuildInputs = [ coq ] ++ coqDeps;
      enableParallelBuilding = true;
      installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
    }
  ) { } ;
  coqide = coqPackages.coqide;
in pkgs // { inherit ssprove coqide; }
