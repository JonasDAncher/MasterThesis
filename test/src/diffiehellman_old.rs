use hacspec_lib::*;

unsigned_public_integer!(DiffInt, 2048);

pub type PK = (DiffInt, DiffInt, DiffInt);
pub type SK = DiffInt;
pub type KeyPair = (PK, SK);
pub type SessionKey = DiffInt;

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
    use num_bigint::*;

    #[test]
    fn diff() {
        let (g, q) = generate_group();
        let (ask, apk) = diff_key_gen(g.clone(), q.clone());
        let (bsk, bpk) = diff_key_gen(g, q);
        let ashared = calculates_shared_key(ask, bpk);
        let bshared = calculates_shared_key(bsk, apk);
        assert_eq!(ashared, bshared);
    }
    fn generate_group() -> (BigUint, BigUint) {
        let mut rng = rand::prelude::thread_rng();
        let g = rng.gen_biguint(1000);
        let q = rng.gen_biguint(1000);
        (g, q)
    }
    
    fn diff_key_gen(g: BigUint, q: BigUint) -> (SK, PK) {
        let sk = generate_private_key(&q);
        let diffg = DiffInt::from(g);
        let diffq = DiffInt::from(q);
        (sk, calculate_pub_key(diffg, diffq, sk))
    }
    
    fn generate_private_key(q: &BigUint) -> SK {
        let mut rng = rand::prelude::thread_rng();
        let sk = rng.gen_biguint_range(&One::one(), &q);
        let diffsk = DiffInt::from(sk);
        diffsk
    }
    
}
