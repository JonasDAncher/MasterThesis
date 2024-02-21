
use hacspec_sha256::*;
use hacspec_lib::*;
use secret_integers::*;

pub type Password = ByteSeq;
pub type Key = ByteSeq;
pub type Salt = ByteSeq;




fn client(salt: Salt, P: Password) {
    let a = U32::classify(5u32); //¯\_(ツ)_/¯;  //generate new session secret
    let g = 5u32;
    let x = hash(&hash(&salt).concat(&hash(&P)));
    let A = g.pow(a.into()); //create new session public key 
    //FIXME into not sure if information flow is okay, private -> public
    // todo!();
    send(&A);
    let (B, u) = recieve();
    let S = (B - g.pow(x.)).pow(a + u * x); 
    let K = hash(&S);
    let M1 = hash((&A, &B, &K));
    send(M1);
    let M2 = hash((&A, &M1, &K));
    let M2recieved = recieve();
    if (M2 == M2recieved) {
        setSessionkey(K); 
    }
}

fn send(m1:_) -> () {
    todo!()
}

fn recieve() -> (u32,u32) {
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