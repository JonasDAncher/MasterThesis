use hacspec_lib::*


bytes!(ElInt, 2048);


pub fn enc(y: ElInt, pk: u128, m: String){
    let Upk = U128(pk);
    let Uy = U128_from_be_bytes(U128Word::from_seq(&y));
    pk.pow_mod(y,et eller andet usynligt);
}



























