use hacspec_lib::*;
use hacspec_sha256::*;
use secret_integers::*;

fn main() {}

unsigned_public_integer!(DiffInt, 2048);

pub type PK = (DiffInt, DiffInt, DiffInt);
pub type SK = (DiffInt, DiffInt, DiffInt);
pub type KeyPair = (PK, SK);
pub type SessionKey = DiffInt;
// pub type ByteSeqResult = Result<ByteSeq, Error>;
// pub type DiffIntResult = Result<DiffInt, Error>;

pub fn revealPublicKey(sk: SK) -> PK {
    let (g, p, z) = sk;
    let hz = g.pow_mod(z, p);
    (g, p, hz)
}

pub fn calculateSharedKey(sk: SK, pk: PK) -> SessionKey {
    let (g, p, sz) = sk;
    let (_, _, pz) = pk;
    // let hab = DiffIntResult::Ok(pz.pow_mod(sz, p));
    let hab = pz.pow_mod(sz, p);
    // hash(&(hab.toSeq()))
    hab
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::*;
    use num_bigint::{BigInt,BigUint,Sign,ToBigInt};
    // use num_traits::{Zero, One};
    #[test]
    fn diff() {
        let (g, p) = generateGroup();
        let ask = diff_key_gen(g,p);
        let apk = revealPublicKey(ask);
        let bsk = diff_key_gen(g,p);
        let bpk = revealPublicKey(bsk);

        let ashared = calculateSharedKey(ask,bpk);
        let bshared = calculateSharedKey(bsk,apk);
        assert_eq!(ashared,bshared);
    }
    fn generateGroup() -> (BigInt,BigInt){
        let mut rng = rand::thread_rng();
        let g = rng.gen_bigint(1000);
        let p = rng.gen_bigint(1000);
        (g,p)
    }

    fn diff_key_gen(g:BigInt,p:BigInt) -> SK {
        let mut rng = rand::thread_rng();
        let x = rng.gen_bigint_range(&One::one(),&p);
        (DiffInt::from(g),DiffInt::from(p),DiffInt::from(x))

        // let x = gen_biguing_range(One::one(),q-One::one());
    }
}
