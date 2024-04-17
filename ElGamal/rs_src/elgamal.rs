use hacspec_lib::*;

bytes!(ElInt, 16);

const Q : u128 = 29u128;
const G : u128 = 2u128;
    
pub fn enc_aux(source_sk: ElInt, target_pk: u128, m: u128) -> (u128, u128) {
    let secret_target_pk = U128::classify(target_pk);
    let secret_source_sk = U128_from_be_bytes(U128Word::from_seq(&source_sk));
    let secret_g 		 = U128::classify(G);
    let secret_m         = U128::classify(m);
	let secret_q 		 = U128::classify(Q);

    let secret_s  		 = secret_target_pk.pow_mod(secret_source_sk,secret_q);
    let secret_c1 		 = secret_g.pow_mod(secret_source_sk, secret_q);
    let secret_c2 		 =  (secret_m * secret_s).modulo(secret_q);
    
    (secret_c1.declassify(),secret_c2.declassify())
}

pub fn keygen() -> (u128, ElInt){
	let secret_sk = U128::classify(4u128);
	let secret_g  = U128::classify(G);
	let secret_q  = U128::classify(Q);
    let pk 		  = (secret_g.pow_mod(secret_sk,secret_q)).declassify();
	let sk 		  = ElInt::from_seq(&U128_to_be_bytes(secret_sk));
    (pk,sk)
}

pub fn enc(target_pk: u128, m: u128) -> (u128, u128){
	let (_gy,y) = keygen();
    enc_aux(y,target_pk,m)
}

pub fn dec(target_sk: ElInt, c: (u128,u128)) -> u128 {
	let secret_q 		 = U128::classify(Q);
	let secret_g  		 = U128::classify(G);
    let (c1,c2) 		 = c;
    let secret_target_sk = U128_from_be_bytes(U128Word::from_seq(&target_sk));
    let secret_c1 		 = U128::classify(c1);
    let secret_c2 		 = U128::classify(c2);

	let secret_s 		 = secret_c1.pow_mod(secret_target_sk,secret_q);
    let secret_s_inverse = secret_s.pow_mod(secret_q-secret_g,secret_q);
    let secret_m 		 = (secret_c2 * secret_s_inverse).pow_mod(U128::classify(1u128),secret_q);
    let m 				 = secret_m.declassify();
    m
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn enc_dec() {
    	let (target_pk, target_sk) = keygen();
    	let m_ideal = 6u128;
    	let c = enc(target_pk, m_ideal);
    	let m_real = dec(target_sk, c);
    	assert_eq!(m_ideal,m_real);
    }
}























