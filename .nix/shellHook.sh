#! /usr/bin/bash

printNixEnv () {
  echo "Here is your work environement"
  echo "buildInputs:"
  for x in $buildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
  echo "propagatedBuildInputs:"
  for x in $propagatedBuildInputs; do printf "  "; echo $x | cut -d "-" -f "2-"; done
  echo "you can pass option --arg config '{coq = \"x.y\"; ...}' to nix-shell to change packages versions"
}
catNixEnv () {
  for x in $buildInputs; do echo $x; done
  for x in $propagatedBuildInputs; do echo $x; done
}

upateNixDefault () {
  cat $currentdir/default.nix
} > default.nix

updateNixPkgs (){
  HASH=$(git ls-remote https://github.com/NixOS/nixpkgs-channels refs/heads/nixpkgs-unstable | cut -f1);
  URL=https://github.com/NixOS/nixpkgs-channels/archive/$HASH.tar.gz
  echo "fetchTarball {
    url = $URL;
    sha256 = \"$SHA256\";
  }" > .nix/nixpkgs.nix
}

updateNixPkgsMaster (){
  HASH=$(git ls-remote https://github.com/NixOS/nixpkgs refs/heads/master | cut -f1)
  URL=https://github.com/NixOS/nixpkgs/archive/$HASH.tar.gz
  SHA256=$(nix-prefetch-url --unpack $URL)
  echo "fetchTarball {
    url = $URL;
    sha256 = \"$SHA256\";
  }" > .nix/nixpkgs.nix
}

updateNixPkgsCustom (){
  if [[ -n "$1" ]]
  then if [[ -n "$2" ]]; then B=$2; else B="master"; fi
       HASH=$(git ls-remote https://github.com/$1/nixpkgs refs/heads/$B | cut -f1)
       URL=https://github.com/$1/nixpkgs/archive/$HASH.tar.gz
       SHA256=$(nix-prefetch-url --unpack $URL)
       echo "fetchTarball {
         url = $URL;
         sha256 = \"$SHA256\";
       }" > .nix/nixpkgs.nix
  else echo "error: usage: updateNixPkgsCustom <github username> [branch]"
  fi
}

printNixOverrides (){
    echo overrides: $overrides
    echo ocaml-overrides: $ocaml_overrides
    echo coq-overrides: $coq_overrides
}

initNixConfig (){
  F=./.nix/config.nix;
  if [[ -f $F ]]
    then echo "$F already exists"
    else if [[ -n "$1" ]]
      then echo "{" > $F
           echo "  pname = \"$1\";" >> $F
           echo "  overrides = {};" >> $F
           echo "}" >> $F
           chmod u+w $F
      else echo "usage: initNixConfig pname"
    fi
  fi
}

fetchCoqOverlay (){
  F=$nixpkgs/pkgs/development/coq-modules/$1/default.nix
  D=./.nix/coq-overlays/$1/
  if [[ -f "$F" ]]
    then mkdir -p $D; cp $F $D; chmod u+w ${D}default.nix;
         git add ${D}default.nix
         echo "You may now amend ${D}default.nix"
    else echo "usage: fetchCoqOverlay pname"
  fi
}