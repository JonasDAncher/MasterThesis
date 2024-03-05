use hacspec_lib::*;
use hacspec_sha256::*;
use num_bigint::*;
use secret_integers::*;

fn main() {}

unsigned_public_integer!(DiffInt, 2048);

pub type PK = (DiffInt, DiffInt, DiffInt);
pub type SK = DiffInt;
pub type KeyPair = (PK, SK);
pub type SessionKey = DiffInt;


fn generateGroup() -> (BigInt, BigInt) {
    let mut rng = rand::thread_rng();
    let g = rng.gen_bigint(1000).abs();
    let p = rng.gen_bigint(1000).abs();
    (g, p)
}

fn diff_key_gen(g: BigInt, p: BigInt) -> (SK, PK) {
    let sk = generatePrivateKey(&p);
    (sk, calculatePubKey(DiffInt::from(g), DiffInt::from(p), sk))

    // let x = gen_biguing_range(One::one(),q-One::one());
}

fn generatePrivateKey(p: &BigInt) -> SK {
    let mut rng = rand::thread_rng();
    let sk = rng.gen_bigint_range(&One::one(), &p);
    DiffInt::from(sk)
}

pub fn calculatePubKey(g: DiffInt, p: DiffInt, sk: SK) -> PK {
    (g, p, g.pow_mod(sk, p))
}

pub fn calculateSharedKey(sk: SK, pk: PK) -> SessionKey {
    let (g, p, pz) = pk;
    let hab = pz.pow_mod(sk, p);
    hab
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::*;
    use num_bigint::{BigInt, BigUint, Sign, ToBigInt};

    #[test]
    fn diff() {
        let (g, p) = generateGroup();
        let (ask, apk) = diff_key_gen(g.clone(), p.clone());
        let (bsk, bpk) = diff_key_gen(g, p);
        let ashared = calculateSharedKey(ask, bpk);
        let bshared = calculateSharedKey(bsk, apk);
        assert_eq!(ashared, bshared);
    }
}
