use hacspec_lib::*;

const Q : u128 = 29u128;
const G : u128 = 2u128;
const SECRET_Q : U128 = U128(Q);
const SECRET_G : U128 = U128(G);
    
pub fn enc_aux(secret_source_sk: U128, target_pk: u128, m: u128) -> (u128, u128) {
    let secret_target_pk = U128::classify(target_pk);
    let secret_m         = U128::classify(m);

    let secret_s  		 = secret_target_pk.pow_mod(secret_source_sk,SECRET_Q);
    let secret_c1 		 = SECRET_G.pow_mod(secret_source_sk, SECRET_Q);
    let secret_c2 		 = (secret_m * secret_s).modulo(SECRET_Q);
    
    (secret_c1.declassify(), secret_c2.declassify())
}

pub fn keygen() -> (u128, U128){
	let secret_sk = U128::classify(4u128);
    let pk 		  = (SECRET_G.pow_mod(secret_sk,SECRET_Q)).declassify();
    (pk,secret_sk)
}

pub fn enc(target_pk: u128, m: u128) -> (u128, u128){
	let (_gy,y) = keygen();
    enc_aux(y,target_pk,m)
}

pub fn dec(secret_target_sk: U128, c: (u128,u128)) -> u128 {
    let (c1,c2) 		 = c;
    let secret_c1 		 = U128::classify(c1);
    let secret_c2 		 = U128::classify(c2);

	let secret_s 		 = secret_c1.pow_mod(secret_target_sk,SECRET_Q);
    let secret_s_inverse = secret_s.pow_mod(SECRET_Q-SECRET_G,SECRET_Q);
    let secret_m 		 = (secret_c2 * secret_s_inverse).pow_mod(U128::classify(1u128),SECRET_Q);
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























