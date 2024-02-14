
const a: u32 = crypto.keygen; //¯\_(ツ)_/¯;  //generate new session secret

fn client(s: salt, P: password) {
    let A = g.pow(a); //create new session public key
    send(A);
    let (B, u) = recieve();
    let S = (B - g.pow(x)).pow(a + ux);
    let K = hash(&S);
    let M1 = hash((&A, &B, &K));
    send(M1);
    let M2 = hash(&A, &M1, &K);
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
