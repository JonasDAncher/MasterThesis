use hacspec_lib::*;


bytes!(ElInt, 2048);


pub fn enc(g:u128 ,y: ElInt, pk: u128, m: String) -> (u128, u128) {
    let Upk = U128(pk);
    let Ug = U128(g);
    let Uy = U128_from_be_bytes(U128Word::from_seq(&y));
    let Um = m.parse::<U128>().unwrap(); //formentlig ændre til U128(..<u128>..)

    let Us = Upk.pow(Uy);
    let Uc1 = Ug.pow(Uy);
    let Uc2 = Um*Us;
    (c1.declassify(),c2.declassify())
}

pub fn dec(x: ElInt, q:u128, c1: u128, c2: u128){
    let Ux = U128_from_be_bytes(U128Word::from_seq(&x));
    let Uc1 = U128(c1);
    let Uc2 = U128(c2);
    let Uq = U128(q);

    let UsInverse = Uc1.pow(Uq-Ux);
    let Um = Uc2*sInverse;
    let m = Um.parse::<U128>().unwrap();
    m
}



























