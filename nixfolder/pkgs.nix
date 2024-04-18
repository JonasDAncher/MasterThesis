let
  pkgs = import ./pin.nix { };
  coqPackages = pkgs.coqPackages.overrideScope' (cfinal: cprev: {
      coq = cprev.coq.override { version = "8.15.2"; };
      mathcomp = cprev.mathcomp.override { 	version = "1.13.0"; };
      mathcomp-analysis = cprev.mathcomp-analysis.override { version = "0.3.13"; };
      mathcomp-word = cprev.mathcomp-word.override { version = "2.0"; };
  });
  jasmin-word = {
    owner = "jasmin-lang";
    repo = "coqword";
    rev = "3d40bc89a3426fd1b0c4f2fd6fb2767dbdf48554";
    sha256 = "rnfC9wo7KAV0OFCIKkj1TullXDXcntn/8ewASFacPao=";
  };
  jasmin-src = {
    owner = "jasmin-lang";
    repo = "jasmin";
    rev = "3d40bc89a3426fd1b0c4f2fd6fb2767dbdf48554";
    sha256 = "rnfC9wo7KAV0OFCIKkj1TullXDXcntn/8ewASFacPao=";
  };
  jasmin-proofs = coqPackages.callPackage ( { coq, stdenv, fetchFromGitHub }:
    stdenv.mkDerivation {
      name = "coq${coq.coq-version}-jasmin";
      src = fetchFromGitHub jasmin-src + "/proofs";

      propagatedBuildInputs = [ coq ] ++ (with coqPackages;
        [ mathcomp.ssreflect mathcomp.algebra mathcomp-word ]);
      enableParallelBuilding = true;
      installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
    }
  ) { } ;
  ssprove = coqPackages.callPackage ( { coq, stdenv, fetchFromGitHub }:
    stdenv.mkDerivation {
      name = "coq${coq.coq-version}-ssprove";

      src = fetchFromGitHub {
        owner = "SSProve";
        repo = "ssprove";
        rev = "bead4e76acbb69b3ecf077cece56cd3fbde501e3";
        sha256 = "sv69x3OqHilOXN9uzATsQxmzK8Z1k6V3ZZMq2dzbo1M=";
      };

      propagatedBuildInputs = [ coq jasmin-proofs ] ++ (with coqPackages;
        [ deriving equations extructures mathcomp.ssreflect mathcomp-analysis mathcomp-word mathcomp-zify ]);
      enableParallelBuilding = true;
      installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
    }
  ) { } ;
  hacspec-src = {
    owner = "hacspec";
    repo = "hacspec";
    rev = "4ecc847fc944fe996e19423aa41f002f2039dab0";
    sha256 = "65rPusiDe54DVO0ApLm/+vwAOc+mD5JOU7KUPJaJbSU=";
  };

  hacspec-coq = coqPackages.callPackage ( { coq, stdenv, fetchFromGitHub }:
    stdenv.mkDerivation {
      name = "coq${coq.coq-version}-hacspec-coq";
      src = fetchFromGitHub hacspec-src + "/coq"; 

        patchPhase = ''
          coq_makefile -f _CoqProject -o Makefile
   #       cat - >> ./src/Hacspec_Lib.v <<EOF
    #      
   #       Locate "^".
 #         Definition uint128_pow_mod
 #           (g_0: int128)
  #          (x_1: int128)
#            (n_2: int128)
#
 #           : int128 :=
 #             (g_0 ^ x_1) mod n_2.
  #        EOF
 #         cat ./src/Hacspec_Lib.v
        '';
      

      propagatedBuildInputs = with coqPackages; [ coq coqprime pkgs.ppl compcert QuickChick ];
      enableParallelBuilding = true;
      installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
    }
  ) { } ;  
  
  hacspec-ssprove = coqPackages.callPackage ( { coq, stdenv, fetchFromGitHub }:
    stdenv.mkDerivation {
      name = "coq${coq.coq-version}-hacspec-ssprove";
      src = fetchFromGitHub hacspec-src + "/coq_ssprove"; 

      patchPhase = ''
        coq_makefile -f _CoqProject -o Makefile
 #       cat - >> ./src/Hacspec_Lib.v <<EOF
 #       
 #       Definition uint128_pow_mod
 #         (g_0: int128)
 #         (x_1: int128)
 #         (n_2: int128)
#
 #         : int128 :=
 #           (g_0 ^ x_1) mod n_2.
 #       EOF
 #       cat ./src/Hacspec_Lib.v
      '';

      propagatedBuildInputs = with coqPackages; [ coq ssprove mathcomp-word pkgs.ppl ];
      enableParallelBuilding = true;
      installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];
    }
  ) { } ;
  

  coqide = coqPackages.coqide;
in pkgs // { inherit ssprove hacspec-ssprove coqide hacspec-coq; }
