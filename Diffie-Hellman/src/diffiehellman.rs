use num_bigint::*;
use hacspec_lib::*;

fn main() {}
unsigned_public_integer!(DiffInt, 2048);

pub type PK = (DiffInt, DiffInt, DiffInt);
pub type SK = DiffInt;
pub type KeyPair = (PK, SK);
pub type SessionKey = DiffInt;


fn generate_group() -> (BigInt, BigInt) {
    let mut rng = rand::prelude::thread_rng();
    let g = rng.gen_bigint(1000).abs();
    let p = rng.gen_bigint(1000).abs();
    (g, p)
}

fn diff_key_gen(g: BigInt, p: BigInt) -> (SK, PK) {
    let sk = generate_private_key(&p);
    (sk, calculate_pub_key(DiffInt::from(g), DiffInt::from(p), sk))
}

fn generate_private_key(p: &BigInt) -> SK {
    let mut rng = rand::prelude::thread_rng();
    let sk = rng.gen_bigint_range(&One::one(), &p);
    DiffInt::from(sk)
}

pub fn calculate_pub_key(g: DiffInt, p: DiffInt, sk: SK) -> PK {
    (g, p, g.pow_mod(sk, p))
}

pub fn calculates_shared_key(sk: SK, pk: PK) -> SessionKey {
    let (_g, p, pz) = pk;
    let hab = pz.pow_mod(sk, p);
    hab
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn diff() {
        let (g, p) = generate_group();
        let (ask, apk) = diff_key_gen(g.clone(), p.clone());
        let (bsk, bpk) = diff_key_gen(g, p);
        let ashared = calculates_shared_key(ask, bpk);
        let bshared = calculates_shared_key(bsk, apk);
        assert_eq!(ashared, bshared);
    }
}
