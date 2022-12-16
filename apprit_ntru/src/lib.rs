extern crate rand;

use itertools::Itertools;
use rand::{thread_rng, Rng};
use rand::distributions::Uniform;

use std::borrow::BorrowMut;
use std::collections::BTreeMap;
use std::fmt::Display;

pub struct NTRU<const P: i64, const Q: i64, const N:i64> {
    keys: Keys<Q>,
}

impl <const P: i64, const Q: i64, const N: i64> NTRU<P, Q, N> {

    pub fn new() -> Self {
        return Self { keys: Keys::new() };
    }

    pub fn get_parameters() -> (i64, i64, i64) {
        return (P, Q, N);
    }

    pub fn generate_keys(&mut self) {
        let x_g = Ring::<Q, N>::generate_n_poly();
        let x_f = Ring::<Q, N>::generate_n_poly();
        let mut f = x_f.mul_scalar(P);
        f.insert(0, f.get(0) + 1);
        let g = x_g.mul_scalar(P);
        print!("f: {}\ng: {}\n", f, g);
        let h = Ring::<Q, N>::multiply_poly_mod(Poly::<Q>::invert_poly(f.clone(), Ring::<Q, N>::inv_poly()), g); 
        self.keys = Keys::from(h, f)
    }

    pub fn encrypt(&self, m: Poly<Q>) -> Result<Poly<Q>, String> {
        if self.keys != Keys::new() {
            let r = Ring::<Q, N>::generate_n_poly();
            return Ok(Ring::<Q, N>::multiply_poly_mod(r, self.keys.pub_key.clone()).add(m));
        }
        return Err(String::from("No keys generated"));
    }

    pub fn decrypt(&self, c: Poly<Q>) -> Result<Poly<P>, String> {
        if self.keys != Keys::new() {
            return Ok(Poly::<P>::from(Ring::<Q, N>::multiply_poly_mod(self.keys.priv_key.clone(), c).values))
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
}

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

    pub fn multiply_poly_mod(poly1: Poly<Q>, poly2: Poly<Q>) -> Poly<Q> {
        let mut poly3 = Poly::new();
        for i in poly1.values.keys() {
            for j in poly2.values.keys() {
                poly3.insert(Self::mod_n(*i+*j), poly3.get(Self::mod_n(*i+*j)) + poly1.get(Self::mod_n(*i)) * poly2.get(Self::mod_n(*j)));
            }
        }
        return poly3;
    }
}

#[derive(PartialEq)]
pub struct Poly<const Q: i64> {
    values: BTreeMap<i64, i64>,
}

impl <const Q: i64> Display for Poly<Q> {

    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        if self.values.len() == 0 {
            return write!(f, "0");
        }

        if self.values.len() == 1 {
            return write!(f, "{}", self.get(self.deg()));
        }

        for (k, v) in self.clone().values.into_iter().rev() {
            if k == 0 {
                let format = if v < 0 { format!("{}", v) } else { format!("+{}", v) };
                match write!(f,  "{}", format) {
                    Ok(_) => 0,
                    Err(e) => panic!("{}", e)
                };
            } else if self.deg() != k {
                let format = if v == 1 { format!("x^{}", k) } else if v == -1 { format!("-x^{}", k) } else { format!("{}x^{}", v, k) };
                let format = if v < 0 { format!("{}", format) } else { format!("+{}", format) };
                match write!(f, "{}", format) {
                    Ok(_) => 0,
                    Err(e) => panic!("{}", e)
                };
            } else {
                let format = if v == 1 || v == -1 { format!("x^{}", k) } else if v == -1 { format!("-x^{}", k) } else { format!("{}x^{}", v, k) };
                match write!(f,  "{}", format) {
                    Ok(_) => 0,
                    Err(e) => panic!("{}", e)
                };
            }
        }
        write!(f, "")
    }
}

impl <const Q: i64> Clone for Poly<Q> {
    
    fn clone(&self) -> Self {
        Poly::from(self.values.clone())
    }
}

impl <const Q: i64> Poly<Q> {

    pub fn new() -> Self {
        Self { values: BTreeMap::new() }
    }

    pub fn from(values: BTreeMap<i64, i64>) -> Self {
        let mut m = Self { values: BTreeMap::new() };
        values.iter().for_each(|(k, v)| m.insert(*k, *v));
        return m;
    }

    pub fn from_vec(values: Vec<(i64, i64)>) -> Self {
        let mut m = Self { values: BTreeMap::new() };
        values.into_iter().for_each(|d| m.insert(d.0, Self::mods(d.1)));
        return m;
    }

    pub fn mul_scalar(&self, s: i64) -> Poly<Q> {
        let mut nmap = Self::new();
        for (k, v) in self.values.iter() {
            nmap.insert(*k, *v * s);
        }
        return nmap;
    }

    pub fn div_scalar(&self, s: i64) -> Poly<Q> {
        let mut nmap = Self::new();
        for (k, v) in self.values.iter() {
            nmap.insert(*k, *v / s);
        }
        return nmap;
    }
    
    pub fn insert(&mut self, k: i64, v: i64) {
        if Self::mods(v) != 0 {
            self.values.insert(k, Self::mods(v));
        } else {
            self.values.remove(&k);
        }
    }

    pub fn get(&self, k: i64) -> i64 {
        return match self.values.get(&k) {
            Some(v) => *v,
            None => 0,
        }
    }

    pub fn mods(a: i64) -> i64 {
        return (a + (Q-1)/2).rem_euclid(Q) - (Q-1)/2
    }

    pub fn add(&self, p: Self) -> Self {
        let mut nmap = Self::new();
        let mut iter1 = self.values.keys().map(|k| *k).into_iter().collect::<Vec<i64>>();
        iter1.append(p.values.keys().map(|k| *k).into_iter().collect::<Vec<i64>>().borrow_mut());
        let indexes = iter1.into_iter().unique().collect::<Vec<i64>>();
        
        for i in indexes {
            nmap.insert(i, self.get(i) + p.get(i));
        }

        return nmap;
    }

    pub fn sub(&self, p: Self) -> Self {
        let mut nmap = Self::new();
        let mut iter1 = self.values.keys().map(|k| *k).into_iter().collect::<Vec<i64>>();
        iter1.append(p.values.keys().map(|k| *k).into_iter().collect::<Vec<i64>>().borrow_mut());
        let indexes = iter1.into_iter().unique().collect::<Vec<i64>>();
        
        for i in indexes {
            nmap.insert(i, self.get(i) - p.get(i));
        }

        return nmap;
    }

    pub fn deg(&self) -> i64 {
        return match self.values.keys().max() {
            Some(v) => *v,
            None => 0,
        }
    }

    pub fn multiply_poly(&self, poly2: Self) -> Self {
        let mut poly3 = Self::new();
        for i in self.values.keys() {
            for j in poly2.values.keys() {
                poly3.insert(*i+*j, poly3.get(*i+*j) + self.get(*i) * poly2.get(*j));
            }
        }
        return poly3;
    }

    pub fn find_coeff(r: i64, v: i64) -> i64 {
        let mut i = 0;
        while Self::mods(1) != Self::mods(v * i) {
            i+=1;
        }
        return i*r;
    }

    pub fn division_poly(p1: Self, p2: Self) -> (Self, Self) {
        let mut r = p1.clone();
        let mut quotient = Self::new();
        let p2d = p2.deg();
        let p2v = p2.get(p2d);
        while r.deg() >= p2d && r != Self::new() {
            let vv = Self::find_coeff(r.get(r.deg()), p2v);
            let v = Self::from_vec(vec![(r.deg()-p2d, vv)]);
            r = r.sub(v.multiply_poly(p2.clone()));
            quotient = quotient.add(v);
        }
        return (quotient, r)
    }

    pub fn extended_gcd(a: Self, b: Self) -> (Self, Self, Self) {
        let mut old_s = Self::from_vec(vec![(0, 1)]);
        let mut old_r = a.clone();
        let mut s = Self::new();
        let mut r = b.clone();
        
        while r != Self::new() {
            let (quotient,remainder) = Self::division_poly(old_r.clone(), r.clone());
            (old_r, r) = (r.clone(), remainder);
            (old_s, s) = (s.clone(), old_s.sub(quotient.multiply_poly(s.clone())));
        }

        return (old_r.clone(), old_s.clone(), Self::division_poly(old_r.sub(old_s.multiply_poly(a.clone())), b.clone()).0)
    }

    pub fn invert_poly(poly1: Self, n: Self) -> Self {
        let mut t = Self::new();
        let mut newt = Self::from_vec(vec![(0, 1)]);
        let mut r = n;
        let mut newr = poly1.clone();
        while newr != Self::new() {
            let (quotient,remainder) = Self::division_poly(r.clone(), newr.clone());
            (r, newr) = (newr.clone(), remainder);
            (t, newt) = (newt.clone(), t.sub(quotient.multiply_poly(newt.clone())));
        }
        return t;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl <const N: i64> Poly<N> {
        pub fn get_all(&self) -> BTreeMap<i64, i64> {
            return self.values.clone();
        }
    }

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

        assert!(values_match(Ring::<Q, N>::multiply_poly_mod(p1, p2).get_all(), p3.get_all()))
    }

    #[test]
    fn generate_n_poly_test() {
        const Q: i64 = 10;
        const N: i64 = 10;
        let p1 = Ring::<Q, N>::generate_n_poly();

        let p2 = Ring::<Q, N>::generate_n_poly();

        assert!(!values_match(p1.get_all(), p2.get_all()))
    }

    // #[test]
    // fn test_h_creation() {
    //     const P: i64 = 3;
    //     const Q: i64 = 31;
    //     const N: i64 = 23;

    //     let f = Poly::<Q>::from_vec(vec![(18, 3), (9, -3), (8, 3), (4, -3), (2, -3), (0, 1)]);
    //     let g = Poly::<Q>::from_vec(vec![(17, 3), (12, 3), (9, 3), (1, -3)]);

    //     let h = Poly::<Q>::from_vec(vec![(22, -13), (21, -15), (19, 12), (18, -14), (16, 8), (15, -14), (14, -6),
    //         (13, 14), (12, -3), (11, 7), (10, -5), (9, -14), (8, 3), (7, 10), (6, 5), (5, -8), (2, 4), (1, 1), (0, 8)]);

    //     let result = Ring::<P,Q,N>::multiply_poly_mod(Ring::<P,Q,N>::invert_poly(f.clone(), Ring::<P, Q, N>::inv_poly()), g);

    //     // println!("inv: {}\n", Ring::<P,Q,N>::invert_poly(f.clone(), Ring::<P, Q, N>::inv_poly()));

    //     assert!(values_match(h.get_all(), result.get_all()))
    // }

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
        const Q: i64 = 67;
        const N: i64 = 23;

        let mut ntru = NTRU::<P, Q, N>::new();
        ntru.generate_keys();
        let m = Ring::<Q, N>::generate_n_poly();

        let c = match ntru.encrypt(m.clone()) {
            Ok(c) => c,
            Err(error) => panic!("Error: {}", error)
        };
        let mp = match ntru.decrypt(c) {
            Ok(mp) => mp,
            Err(error) => panic!("Error: {}", error)
        };

        print!("\nm: {}\nmp: {}\n", m, mp);
        
        assert!(values_match(m.values, mp.values));
    }

    #[test]
    fn test_extended_gcd() {
        const Q: i64 = 31;
        const N: i64 = 23;

        let b = Poly::<Q>::from_vec(vec![(18, 3), (9, -3), (8, 3), (4, -3), (2, -3), (0, 1)]);
        let a = Ring::<Q, N>::inv_poly();

        let (r, s, t) = Poly::<Q>::extended_gcd(a.clone(), b.clone());

        println!("\nr: {}\ns: {}\na: {}\nt: {}\nb: {}\n s*a+t*b: {}", r, s, a, t,b, s.multiply_poly(a.clone()).add(t.multiply_poly(b.clone())));
    }

    #[test]
    fn test_extended_gcd2() {
        const Q: i64 = 2;

        let b = Poly::<Q>::from_vec(vec![(6, 1), (4, 1), (1, 1), (0, 1)]);
        let a = Poly::<Q>::from_vec(vec![(8, 1), (4, 1), (3, 1), (1, 1), (0, 1)]);

        let (r, s, t) = Poly::<Q>::extended_gcd(a.clone(), b.clone());

        println!("\nr: {}\ns: {}\na: {}\nt: {}\nb: {}\n s*a+t*b: {}", r, s, a, t,b, s.multiply_poly(a.clone()).add(t.multiply_poly(b.clone())));

        let inv = Poly::<Q>::invert_poly(b.clone(), a);

        assert!(values_match(inv.clone().values, t.values) && values_match(inv.values, Poly::<Q>::from_vec(vec![(7, 1), (6, 1), (3, 1), (1, 1)]).values))
    }
}
