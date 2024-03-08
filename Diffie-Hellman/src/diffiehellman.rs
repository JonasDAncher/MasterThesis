use num_bigint::*;
use hacspec_lib::*;

unsigned_public_integer!(DiffInt, 2048);

pub type PK = (DiffInt, DiffInt, DiffInt);
pub type SK = DiffInt;
pub type KeyPair = (PK, SK);
pub type SessionKey = DiffInt;


fn generate_group() -> (BigUint, BigUint) {
    let mut rng = rand::prelude::thread_rng();
    let g = rng.gen_biguint(1000);
    let q = rng.gen_biguint(1000);
    // let g = 10000.to_biguint().unwrap();
    // let q = 1156651.to_biguint().unwrap();
    (g, q)
}

fn diff_key_gen(g: BigUint, q: BigUint) -> (SK, PK) {
    let sk = generate_private_key(&q);
    let gd = DiffInt::from(g);
    let qd = DiffInt::from(q.clone());
    (sk, calculate_pub_key(gd, qd, sk))
}

fn generate_private_key(q: &BigUint) -> SK {
    let mut rng = rand::prelude::thread_rng();
    let sk = rng.gen_biguint_range(&One::one(), &q);
    // let sk = 1315000.to_biguint().unwrap();
    let asf = DiffInt::from(sk);
    asf
}

pub fn calculate_pub_key(g: DiffInt, q: DiffInt, sk: SK) -> PK {
    (g, q, g.pow_mod(sk, q))
}

pub fn calculates_shared_key(sk: SK, pk: PK) -> SessionKey {
    let (_g, q, pz) = pk;
    let hab:SessionKey = pz.pow_mod(sk, q);
    hab
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diff() {
        let (g, q) = generate_group();
        let (ask, apk) = diff_key_gen(g.clone(), q.clone());
        let (bsk, bpk) = diff_key_gen(g, q);
        let ashared = calculates_shared_key(ask, bpk);
        let bshared = calculates_shared_key(bsk, apk);
        assert_eq!(ashared, bshared);
    }
}
