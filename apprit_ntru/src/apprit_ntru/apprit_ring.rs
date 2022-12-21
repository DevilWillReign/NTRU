pub mod ring {
    use rand::{thread_rng, distributions::Uniform, Rng};

    use crate::apprit_ntru::apprit_poly::poly::Poly;

    pub struct Ring<const Q: i64, const N: i64> {
    }
    
    impl <const Q: i64, const N: i64> Ring<Q, N> {
    
        pub fn inv_poly() -> Poly<Q> {
            Poly::from_vec(vec![(N, 1), (0, -1)])
        }
    
        pub fn generate_n_poly() -> Poly<Q> {
            let mut poly = Poly::new();
            let mut rng = thread_rng();
            let side = Uniform::new_inclusive(-1, 1);
            for i in 0..N {
                poly.insert(i, rng.sample(side));
            }
            return poly;
        }
    
        fn mod_n(a: i64) -> i64 {
            a.rem_euclid(N)
        }
    
        pub fn multiply_poly_mod(poly1: &Poly<Q>, poly2: &Poly<Q>) -> Poly<Q> {
            let mut poly3 = Poly::new();
            for i in poly1.keys() {
                for j in poly2.keys() {
                    poly3.insert(Self::mod_n(*i+*j), poly3.get(Self::mod_n(*i+*j)) + poly1.get(Self::mod_n(*i)) * poly2.get(Self::mod_n(*j)));
                }
            }
            return poly3;
        }
    
        pub fn poly_mod(poly1: Poly<Q>) -> Poly<Q> {
            let mut poly3 = Poly::new();
            for i in poly1.keys() {
                poly3.insert(Self::mod_n(*i), poly3.get(Self::mod_n(*i)) + poly1.get(Self::mod_n(*i)));
            }
            return poly3;
        }
    }
}