use apprit_ntru::{self, apprit_ntru::{apprit_ntru::NTRU, apprit_poly::poly::Poly}};

fn main() {
    const P: i64 = 3;
    const Q: i64 = 257;
    const N: i64 = 23;

    let mut ntru = NTRU::<P, Q, N>::new();
    ntru.generate_keys();
    let m = Poly::<Q>::from_vec(vec![(15, 1), (12, -1), (7, 1), (0, -1)]);
    let r = Poly::<Q>::from_vec(vec![(19, 1), (10, 1), (6, 1), (2, -1)]);

    let c = match ntru.encrypt(&m, &r, &ntru.keys().pub_key()) {
        Ok(c) => c,
        Err(error) => panic!("Error: {}", error)
    };

    let mp = match ntru.decrypt(&c, &ntru.keys().priv_key()) {
        Ok(mp) => mp,
        Err(error) => panic!("Error: {}", error)
    };

    println!("m: {}\nc: {}\nmp: {}\n", m, c, mp);
    println!("Hello, world!");
}
