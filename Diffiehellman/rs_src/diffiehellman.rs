use hacspec_lib::*;
//mod powmod;
// unsigned_public_integer!(DiffInt, 2048); // Doesn't work
bytes!(DiffInt, 2048); 
// bytes!(SK, 2048); 
// bytes!(SessionKey, 2048); 

pub type PK = (u128, u128, u128);
// pub type SK = DiffInt;
// pub type SessionKey = DiffInt;

pub fn calculate_pub_key(g: u128, q: u128, sk: DiffInt) -> PK { //sk should be type SK
    let Ug = U128(g);
    let Uq = U128(q);
    let Usk = U128_from_be_bytes(U128Word::from_seq(&sk));
    let Ugz = Ug.pow_mod(Usk, Uq);
    let gz = Ugz.declassify();
    (g, q, gz)
}

pub fn calculates_shared_key(sk: DiffInt, pk: PK) -> DiffInt { //returns a session key and sk should be type SK
    let (_g, q, pz) = pk;
    let Uq = U128(q);
    let Upz = U128(pz);
    let Usk = U128_from_be_bytes(U128Word::from_seq(&sk));
    let hab = Upz.pow_mod(Usk, Uq);
    DiffInt::from_seq(&U128_to_be_bytes(hab))
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use num_bigint::*;
//
//     pub type KeyPair = (PK, SK);
//
//     #[test]
//     fn diff() {
//         let (g, q) = generate_group();
//         let (ask, apk) = diff_key_gen(g.clone(), q.clone());
//         let (bsk, bpk) = diff_key_gen(g, q);
//         let ashared = calculates_shared_key(ask, bpk);
//         let bshared = calculates_shared_key(bsk, apk);
//         assert_eq!(ashared, bshared);
//     }
//     fn generate_group() -> (BigUint, BigUint) {
//         let mut rng = rand::prelude::thread_rng();
//         let g = rng.gen_biguint(1000);
//         let q = rng.gen_biguint(1000);
//         (g, q)
//     }
    
//     fn diff_key_gen(g: BigUint, q: BigUint) -> (SK, PK) {
//         let sk = generate_private_key(&q);
//         let diffg = DiffInt::from(g);
//         let diffq = DiffInt::from(q);
//         (sk, calculate_pub_key(diffg, diffq, sk))
//     }
    
//     fn generate_private_key(q: &BigUint) -> SK {
//         let mut rng = rand::prelude::thread_rng();
//         let sk = rng.gen_biguint_range(&One::one(), &q);
//         let diffsk = DiffInt::from(sk);
//         diffsk
//     }
    
// }
