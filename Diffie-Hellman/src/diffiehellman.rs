use num_bigint::*;
use hacspec_lib::*;

unsigned_public_integer!(DiffInt, 2048);

pub type PK = (DiffInt, DiffInt, DiffInt);
pub type SK = DiffInt;
pub type KeyPair = (PK, SK);
pub type SessionKey = DiffInt;


fn generate_group() -> (BigInt, BigInt) {
    // let mut rng = rand::prelude::thread_rng();
    // let g = rng.gen_bigint(1000).abs();
    // let q = rng.gen_bigint(1000).abs();
    let g = 10000.to_bigint().unwrap();
    let q = 1156651.to_bigint().unwrap();
    (g, q)
}

fn diff_key_gen(g: BigInt, q: BigInt) -> (SK, PK) {
    let sk = generate_private_key(&q);
    (sk, calculate_pub_key(DiffInt::from(g), DiffInt::from(q), sk))
}

fn generate_private_key(q: &BigInt) -> SK {
    // let mut rng = rand::prelude::thread_rng();
    // let sk = rng.gen_bigint_range(&One::one(), &q);
    let sk = 1315000.to_bigint().unwrap();
    let asd = DiffInt::from(sk) as SK;
    asd
}

pub fn calculate_pub_key(g: DiffInt, q: DiffInt, sk: SK) -> PK {
    (g, q, g.pow_mod(sk, q))
}

pub fn calculates_shared_key(sk: SK, pk: PK) -> SessionKey {
    let (_g, q, pz) = pk;
    let hab = pz.pow_mod(sk, q);
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
