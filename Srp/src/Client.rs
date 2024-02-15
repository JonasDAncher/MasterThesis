
use hacspec_sha256::*;
use hacspec_lib::*;

const a: U32 = 5; //¯\_(ツ)_/¯;  //generate new session secret

fn client(salt: &ByteSeq, P: password) {
    let g = 5;
    let x = hash((salt, P));
    let A = g.pow(a); //create new session public key
    send(A);
    let (B, u) = recieve();
    let S = (B - g.pow(x)).pow(a + u * x);
    let K = hash(&S);
    let M1 = hash((&A, &B, &K));
    send(M1);
    let M2 = hash((&A, &M1, &K));
    let M2recieved = recieve();
    if (M2 == M2recieved) {
        setSessionkey(K); 
    }
}

fn send(m1: _) -> _ {
    todo!()
}

fn recieve() -> _ {
    todo!()
}

fn setSessionkey(k: _) -> _ { 
    todo!()
}


/*
change list:
- const a u32 -> U32 (hacspec secret u32)
- salt is now a &ByteSeq (hacspec/examples/hkdf.rs l. 18)
- let x added, is a hash of salt and P as per diagram.
 */