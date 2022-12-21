pub mod apprit_ntru;

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::apprit_ntru::{apprit_poly::poly::Poly, apprit_ring::ring::Ring, apprit_ntru::NTRU};

    fn values_match(values1: BTreeMap<i64, i64>, values2: BTreeMap<i64, i64>) -> bool {
        return values1.len() == values2.len() &&
            values1.iter().all(|(k,v)| {
                if values2.contains_key(k) {
                    return match values2.get(k) {
                        Some(v2) => *v == *v2,
                        None => false,
                    }
                }
                return false;
            });
    }

    #[test]
    fn multiply_poly_test() {
        const N: i64 = 3;
        const Q: i64 = 19;

        let mut p1 = Poly::<Q>::new();
        p1.insert(2, 1);
        p1.insert(1, 3);
        p1.insert(0, 1);

        let mut p2 = Poly::<Q>::new();
        p2.insert(2, 2);
        p2.insert(1, 1);
        p2.insert(0, -4);


        let mut p3 = Poly::<Q>::new();
        p3.insert(2, 1);
        p3.insert(1, -9);
        p3.insert(0, 3);

        assert!(values_match(Ring::<Q, N>::multiply_poly_mod(&p1, &p2).get_all(), p3.get_all()))
    }

    #[test]
    fn generate_n_poly_test() {
        const Q: i64 = 10;
        const N: i64 = 10;
        let p1 = Ring::<Q, N>::generate_n_poly();

        let p2 = Ring::<Q, N>::generate_n_poly();

        assert!(!values_match(p1.get_all(), p2.get_all()))
    }

    #[test]
    fn test_h_creation() {
        const Q: i64 = 31;
        const N: i64 = 23;

        let f = Poly::<Q>::from_vec(vec![(18, 3), (9, -3), (8, 3), (4, -3), (2, -3), (0, 1)]);
        let g = Poly::<Q>::from_vec(vec![(17, 3), (12, 3), (9, 3), (1, -3)]);

        let invf = Poly::<Q>::from_vec(vec![(22, 14), (21, 22), (20, 23), (19, 27), (18, 11), (17, 18), (16, 22), (15, 12),
            (14, 25), (13, 1), (12, 30), (11, 5), (10, 19), (9, 13), (8, 20), (7, 15), (6, 5), (5, 12), (4, 26), (3, 15), (2, 21),
            (1, 4), (0, 27)]);

        let invf2 = Poly::<Q>::invert_poly(&f, &Ring::<Q, N>::inv_poly());

        assert!(values_match(invf.clone().get_all(), invf2.get_all()));

        let result = Ring::<Q,N>::multiply_poly_mod(&invf, &g);

        assert!(values_match(Ring::<Q,N>::multiply_poly_mod(&f, &result).get_all(), g.get_all()))
    }

    #[test]
    fn test_mods() {
        const Q: i64 = 5;
        assert!(Poly::<Q>::mods(0) == 0);
        assert!(Poly::<Q>::mods(1) == 1);
        assert!(Poly::<Q>::mods(2) == 2);
        assert!(Poly::<Q>::mods(3) == -2);
        assert!(Poly::<Q>::mods(4) == -1);

        const Q2: i64 = 6;
        assert!(Poly::<Q2>::mods(0) == 0);
        assert!(Poly::<Q2>::mods(1) == 1);
        assert!(Poly::<Q2>::mods(2) == 2);
        assert!(Poly::<Q2>::mods(3) == 3);
        assert!(Poly::<Q2>::mods(4) == -2);
        assert!(Poly::<Q2>::mods(5) == -1);
    }

    #[test]
    fn test_ntru() {
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

        println!("m: {}\nc: {}\n", m, c);
        
        assert!(values_match(m.get_all(), mp.get_all()));
    }

    #[test]
    fn test_ntru_pred() {
        const P: i64 = 3;
        const Q: i64 = 31;
        const N: i64 = 23;

        let ntru = NTRU::<P, Q, N>::new();

        let f = Poly::<Q>::from_vec(vec![(18, 3), (9, -3), (8, 3), (4, -3), (2, -3), (0, 1)]);
        let g = Poly::<Q>::from_vec(vec![(17, 3), (12, 3), (9, 3), (1, -3)]);

        let invf = Poly::<Q>::invert_poly(&f, &Ring::<Q, N>::inv_poly());

        let h = Ring::<Q, N>::multiply_poly_mod(&invf, &g);

        let m = Poly::<Q>::from_vec(vec![(15, 1), (12, -1), (7, 1), (0, -1)]);
        let r = Poly::<Q>::from_vec(vec![(19, 1), (10, 1), (6, 1), (2, -1)]);

        let c = match ntru.encrypt(&m, &r, &h) {
            Ok(c) => c,
            Err(error) => panic!("Error: {}", error)
        };
        let mp = match ntru.decrypt(&c, &f) {
            Ok(mp) => mp,
            Err(error) => panic!("Error: {}", error)
        };
        
        assert!(values_match(m.get_all(), mp.get_all()));
    }

    #[test]
    fn test_extended_gcd() {
        const Q: i64 = 31;
        const N: i64 = 23;

        let b = Poly::<Q>::from_vec(vec![(18, 3), (9, -3), (8, 3), (4, -3), (2, -3), (0, 1)]);
        let a = Ring::<Q, N>::inv_poly();

        let (r, s, t) = Poly::<Q>::extended_poly_gcd(&a, &b);

        println!("\nr: {}\ns: {}\na: {}\nt: {}\nb: {}\n s*a+t*b: {}", r, s, a.sub(&t), t,b, s.multiply_poly(&a).add(&t.multiply_poly(&b)));

        let sa = Poly::<Q>::from_vec(vec![(17, 20), (16, 27), (15, 24), (14, 12), (13, 29), (12, 8), (11, 27), (10, 26),
            (9, 18), (8, 8), (7, 27), (6, 19), (5, 17), (4, 6), (3, 3), (2, 2), (1, 4), (0, 26)]);
        
        let tb = Poly::<Q>::from_vec(vec![(22, 14), (21, 22), (20, 23), (19, 27), (18, 11), (17, 18), (16, 22), (15, 12),
            (14, 25), (13, 1), (12, 30), (11, 5), (10, 19), (9, 13), (8, 20), (7, 15), (6, 5), (5, 12), (4, 26), (3, 15), (2, 21),
            (1, 4), (0, 27)]);

        assert!(values_match(s.get_all(), sa.get_all()));
        assert!(values_match(t.get_all(), tb.get_all()));
        println!("\ns: {}\na: {}\nt: {}\nb: {}\ns*a+t*b: {}\n", sa, &a, tb, &b, sa.multiply_poly(&a).add(&tb.multiply_poly(&b)));
    }

    #[test]
    fn test_extended_gcd2() {
        const Q: i64 = 2;

        let b = Poly::<Q>::from_vec(vec![(6, 1), (4, 1), (1, 1), (0, 1)]);
        let a = Poly::<Q>::from_vec(vec![(8, 1), (4, 1), (3, 1), (1, 1), (0, 1)]);

        let (_, _, t) = Poly::<Q>::extended_poly_gcd(&a, &b);

        let inv = Poly::<Q>::invert_poly(&b, &a);

        assert!(values_match(inv.clone().get_all(), t.get_all()) && values_match(inv.get_all(), Poly::<Q>::from_vec(vec![(7, 1), (6, 1), (3, 1), (1, 1)]).get_all()))
    }

    #[test]
    fn test_gcd() {
        const Q:i64 = 64;

        println!("{}", Poly::<Q>::gcd(-20, Q))
    }
}