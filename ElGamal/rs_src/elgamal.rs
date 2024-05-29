use hacspec_lib::*;

const Q : u128 = 29u128;
const G : u128 = 2u128;
const SECRET_Q : U128 = U128(Q);
const SECRET_G : U128 = U128(G);
const sk:u128 = 4u128;


pub fn keygen() -> (u128, U128){
	let secret_sk = U128::classify(sk);
	let pk 		  = (SECRET_G.pow_mod(secret_sk,SECRET_Q)).declassify();
	(pk,secret_sk)
}

pub fn enc(target_pk: u128, m: u128) -> (u128, u128){
	let (source_pk,secret_source_sk) = keygen();
	let secret_target_pk = U128::classify(target_pk);
	let secret_m         = U128::classify(m);

	let secret_s  	     = secret_target_pk.pow_mod(secret_source_sk,SECRET_Q);
	let c1 		     = source_pk;
	let c2 		     = (secret_m * secret_s).declassify();
    
	(c1, c2)
}

pub fn dec(secret_target_sk: U128, c: (u128,u128)) -> u128 {
	let (c1,c2) 		 = c;
	let secret_c1 		 = U128::classify(c1);
	let secret_c2 		 = U128::classify(c2);

	let secret_s_inverse 	 = secret_c1.pow_mod((-secret_target_sk),SECRET_Q);
	let secret_m 		 = secret_c2 * secret_s_inverse;
	let m 			 = secret_m.declassify();
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























