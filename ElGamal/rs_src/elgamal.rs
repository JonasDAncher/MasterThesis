use hacspec_lib::*;


bytes!(ElInt, 2048);
const g:u128 = 6515131653u128;
const q:u128 = 507800679889911926255u128;
    
pub fn enc_aux(y: ElInt, pk: u128, m: u128) -> (u128, u128) {
    let Upk = U128::classify(pk);
    let Ug = U128::classify(g);
    let Uy = U128_from_be_bytes(U128Word::from_seq(&y));
    let Um = U128::classify(m);

    let Us = Upk ^ Uy;
    let Uc1 = Ug ^ Uy;
    let Uc2 = Um*Us;
    (Uc1.declassify(),Uc2.declassify())
}

pub fn enc(pk: u128, m: u128) -> (u128, u128){
    let y = ElInt::from_seq(&U128_to_be_bytes(U128::classify(9846516496u128)));
    enc_aux(y,pk,m)
}

pub fn gen() -> (u128, ElInt){
	let Usk = U128::classify(407800679889911926255u128);
    let pk = (U128::classify(g) ^ Usk).declassify();
	let sk = ElInt::from_seq(&U128_to_be_bytes(Usk));
    (pk,sk)
}

pub fn dec(x: ElInt, c: (u128,u128)) -> u128 {
	let Uq = U128::classify(q);
    let (c1,c2) = c;
    let Ux = U128_from_be_bytes(U128Word::from_seq(&x));
    let Uc1 = U128::classify(c1);
    let Uc2 = U128::classify(c2);

    let UsInverse = Uc1 ^ (Uq-Ux);
    let Um = Uc2*UsInverse;
    let m = Um.declassify();
    m
}



























