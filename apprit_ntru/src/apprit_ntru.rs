extern crate rand;

pub mod apprit_poly;
pub mod apprit_ring;

pub mod apprit_ntru {
    use crate::apprit_ntru::{apprit_ring::ring::Ring, apprit_poly::poly::Poly};

    pub struct NTRU<const P: i64, const Q: i64, const N:i64> {
        keys: Keys<Q>,
    }

    impl <const P: i64, const Q: i64, const N: i64> NTRU<P, Q, N> {

        pub fn new() -> Self {
            return Self { keys: Keys::new() };
        }

        pub fn get_parameters(&self) -> (i64, i64, i64) {
            return (P, Q, N);
        }

        pub fn keys(&self) -> &Keys<Q> {
            return &self.keys;
        }

        pub fn generate_keys(&mut self) {
            let x_g = Ring::<Q, N>::generate_n_poly();
            let x_f = Ring::<Q, N>::generate_n_poly();
            let mut f = x_f.mul_scalar(P);
            f.insert(0, f.get(0) + 1);
            println!("{}", f);
            let g = x_g.mul_scalar(P);
            let h = Ring::<Q, N>::multiply_poly_mod(&Poly::<Q>::invert_poly(&f, &Ring::<Q, N>::inv_poly()), &g);
            self.keys = Keys::from(h, f)
        }

        pub fn encrypt(&self, m: &Poly<Q>, r: &Poly<Q>, pub_key: &Poly<Q>) -> Result<Poly<Q>, String> {
            if *pub_key != Poly::<Q>::new() {
                return Ok(Ring::<Q, N>::multiply_poly_mod(&r, &pub_key).add(&m));
            }
            return Err(String::from("No keys generated"));
        }

        pub fn decrypt(&self, c: &Poly<Q>, priv_key: &Poly<Q>) -> Result<Poly<P>, String> {
            if *priv_key != Poly::<Q>::new() {
                return Ok(Poly::<P>::from(Ring::<Q, N>::multiply_poly_mod(&priv_key, &c).get_all()))
            }
            return Err(String::from("No keys generated"));
        }
    } 

    #[derive(PartialEq)]
    pub struct Keys<const Q: i64> {
        pub_key: Poly<Q>,
        priv_key: Poly<Q>,
    }

    impl <const Q: i64> Keys<Q> {

        pub fn new() -> Self {
            Self::from(Poly::new(), Poly::new())
        }

        pub fn from(pub_key: Poly<Q>, priv_key: Poly<Q>) -> Self {
            Self { pub_key: pub_key, priv_key: priv_key }
        }

        pub fn pub_key(&self) -> &Poly<Q> {
            return &self.pub_key;
        }

        pub fn priv_key(&self) -> &Poly<Q> {
            return &&self.priv_key;
        }
    }
}
