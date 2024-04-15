!#/bin/bash/

grep -qxF "alias coq='cd ~/Documents/MasterThesisProject/hacspec/coq/" ~/.bashrc ||
	echo "alias coq='cd ~/Documents/MasterThesisProject/hacspec/coq/'"

grep -qxF "alias coqss='cd ~/Documents/MasterThesisProject/hacspec/coq_ssprove/" ~/.bashrc ||
	echo "alias coqss='cd ~/Documents/MasterThesisProject/hacspec/coq_ssprove/'"

grep -qxF "alias diff='cd ~/Documents/MasterThesisProject/hacspec/Diffiehellman/" ~/.bashrc ||
	echo "alias diff='cd ~/Documents/MasterThesisProject/MasterThesis/Diffiehellman/'"
	
grep -qxF "alias elga='cd ~/Documents/MasterThesisProject/MasterThesis/ElGamal/" ~/.bashrc ||
	echo "alias elga='cd ~/Documents/MasterThesisProject/MasterThesis/ElGamal/'"

cat <<EOF echo
function haccoq
{
	cargo hacspec --dir ./coq_src -e v
	sed -i '9 a  From Diffie Require Import powmod.' ~/Documents/MasterThesisProject/MasterThesis/Diffiehellman/coq_src/Diffiehellman.v
}
EOF
