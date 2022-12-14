extern crate rand;

use itertools::Itertools;
use rand::{thread_rng, Rng};
use rand::distributions::Uniform;

use std::borrow::BorrowMut;
use std::collections::BTreeMap;

pub struct NTRU<const P: i32, const Q: i32, const N:i32> {
    keys: Keys<Q>,
}

impl <const P: i32, const Q: i32, const N: i32> NTRU<P, Q, N> {

    pub fn new() -> Self {
        return Self { keys: Keys::new() };
    }

    pub fn get_parameters() -> (i32, i32, i32) {
        return (P, Q, N);
    }

    pub fn generate_keys(&mut self) {
        self.keys = Ring::<P, Q, N>::generate_keys();
    }

    pub fn encrypt(&self, m: Poly<Q>) -> Result<Poly<Q>, String> {
        if self.keys != Keys::new() {
            let r = Ring::<P, Q, N>::generate_n_poly();
            return Ok(Ring::<P, Q, N>::multiply_poly_mod(r, self.keys.pub_key.clone()).add(m));
        }
        return Err(String::from("No keys generated"));
    }

    pub fn decrypt(&self, c: Poly<Q>) -> Result<Poly<P>, String> {
        if self.keys != Keys::new() {
            return Ok(Poly::<P>::from(Ring::<P, Q, N>::multiply_poly_mod(self.keys.priv_key.clone(), c).values))
        }
        return Err(String::from("No keys generated"));
    }
} 

#[derive(PartialEq)]
pub struct Keys<const Q: i32> {
    pub_key: Poly<Q>,
    priv_key: Poly<Q>,
}

impl <const Q: i32> Keys<Q> {

    pub fn new() -> Self {
        Self { pub_key: Poly::new(), priv_key: Poly::new() }
    }
}

pub struct Ring<const P: i32, const Q: i32, const N: i32> {
}

impl <const P: i32, const Q: i32, const N: i32> Ring<P, Q, N> {

    pub fn inv_poly() -> Poly<Q> {
        Poly::from_vec(vec![(N, 1), (0, -1)])
    }

    pub fn find_coeff(r: i32, v: i32) -> i32 {
        let mut i = 0;
        while Poly::<Q>::mods(1) != Poly::<Q>::mods(v * i) {
            i+=1;
        }
        return i*r;
    }

    pub fn division_poly(p1: Poly<Q>, p2: Poly<Q>) -> (Poly<Q>, Poly<Q>) {
        let mut r = p1.clone();
        let mut quotient = Poly::<Q>::new();
        let p2d = p2.deg();
        let p2v = p2.get(p2d);
        while r.deg() >= p2d && r != Poly::<Q>::new() {
            let vv = Self::find_coeff(r.get(r.deg()), p2v);
            let v = Poly::from_vec(vec![(r.deg()-p2d, vv)]);
            r = r.add(v.multiply_poly(p2.clone()).neg());
            quotient = quotient.add(v);
        }
        return (quotient, r)
    }

    pub fn invert_poly(poly1: Poly<Q>) -> Poly<Q> {
        let mut t = Poly::new();
        let mut newt = Poly::from_vec(vec![(0, 1)]);
        let mut r = Self::inv_poly();
        let mut newr = poly1.clone();
        while newr != Poly::new() {
            let (quotient,remainder) = Self::division_poly(r.clone(), newr.clone());
            (r, newr) = (newr.clone(), remainder);
            (t, newt) = (newt.clone(), t.add(quotient.multiply_poly(newt.clone()).neg()));
        }
        return t;
    }

    pub fn generate_keys() -> Keys<Q> {
        let x_g = Self::generate_n_poly();
        let x_f = Self::generate_n_poly();
        let mut f = x_f.mul_scalar(P);
        f.insert(0, f.get(0) + 1);
        let g = x_g.mul_scalar(P);
        let h = Self::multiply_poly_mod(Self::invert_poly(f.clone()), g); 
        return Keys { pub_key: f, priv_key: h }
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

    pub fn multiply_poly_mod(poly1: Poly<Q>, poly2: Poly<Q>) -> Poly<Q> {
        let mut poly3 = Poly::new();
        for i in poly1.values.keys() {
            for j in poly2.values.keys() {
                poly3.insert((*i+*j).rem_euclid(N), poly3.get((*i+*j).rem_euclid(N)) + poly1.get((*i).rem_euclid(N)) * poly2.get((*j).rem_euclid(N)));
            }
        }
        return poly3;
    }
}

#[derive(PartialEq, Debug)]
pub struct Poly<const Q: i32> {
    values: BTreeMap<i32, i32>,
}

impl <const Q: i32> Clone for Poly<Q> {
    
    fn clone(&self) -> Self {
        Poly::from(self.values.clone())
    }
}

impl <const Q: i32> Poly<Q> {

    pub fn new() -> Self {
        Self { values: BTreeMap::new() }
    }

    pub fn from(values: BTreeMap<i32, i32>) -> Self {
        let mut m = Self { values: BTreeMap::new() };
        values.iter().for_each(|(k, v)| m.insert(*k, *v));
        return m;
    }

    pub fn from_vec(values: Vec<(i32, i32)>) -> Self {
        let mut m = Self { values: BTreeMap::new() };
        values.into_iter().for_each(|d| m.insert(d.0, Self::mods(d.1)));
        return m;
    }

    pub fn mul_scalar(&self, s: i32) -> Poly<Q> {
        let mut nmap = Poly::new();
        for (k, v) in self.values.iter() {
            nmap.insert(*k, *v * s);
        }
        return nmap;
    }
    
    pub fn insert(&mut self, k: i32, v: i32) {
        if Self::mods(v) != 0 {
            self.values.insert(k, Self::mods(v));
        } else {
            self.values.remove(&k);
        }
    }

    pub fn get(&self, k: i32) -> i32 {
        return match self.values.get(&k) {
            Some(v) => *v,
            None => 0,
        }
    }

    pub fn mods(a: i32) -> i32 {
        return (a + (Q-1)/2).rem_euclid(Q) - (Q-1)/2
    }

    pub fn neg(&self) -> Poly<Q> {
        let mut nmap = Poly::new();
        for (k, v) in self.values.iter() {
            nmap.insert(*k, Q-*v);
        }
        return nmap;
    }

    pub fn add(&self, p: Poly<Q>) -> Self {
        let mut nmap = Poly::new();
        let mut iter1 = self.values.keys().map(|k| *k).into_iter().collect::<Vec<i32>>();
        iter1.append(p.values.keys().map(|k| *k).into_iter().collect::<Vec<i32>>().borrow_mut());
        let indexes = iter1.into_iter().unique().collect::<Vec<i32>>();
        
        for i in indexes {
            nmap.insert(i, self.get(i) + p.get(i));
        }

        return nmap;
    }

    pub fn deg(&self) -> i32 {
        return match self.values.keys().max() {
            Some(v) => *v,
            None => 0,
        }
    }

    pub fn multiply_poly(&self, poly2: Poly<Q>) -> Poly<Q> {
        let mut poly3 = Poly::new();
        for i in self.values.keys() {
            for j in poly2.values.keys() {
                poly3.insert(*i+*j, poly3.get(*i+*j) + self.get(*i) * poly2.get(*j));
            }
        }
        return poly3;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    impl <const N: i32> Poly<N> {
        pub fn get_all(&self) -> BTreeMap<i32, i32> {
            return self.values.clone();
        }
    }

    fn values_match(values1: BTreeMap<i32, i32>, values2: BTreeMap<i32, i32>) -> bool {
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
        const N: i32 = 3;
        const Q: i32 = 19;

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

        assert!(values_match(Ring::<9, Q, N>::multiply_poly_mod(p1, p2).get_all(), p3.get_all()))
    }

    #[test]
    fn generate_n_poly_test() {
        const Q: i32 = 10;
        let p1 = Ring::<1, Q, 10>::generate_n_poly();

        let p2 = Ring::<1, Q, 10>::generate_n_poly();

        assert!(!values_match(p1.get_all(), p2.get_all()))
    }

    #[test]
    fn test_h_creation() {
        const P: i32 = 3;
        const Q: i32 = 31;
        const N: i32 = 23;

        let f = Poly::<Q>::from_vec(vec![(18, 3), (9, -3), (8, 3), (4, -3), (2, -3), (0, 1)]);
        let g = Poly::<Q>::from_vec(vec![(17, 3), (12, 3), (9, 3), (1, -3)]);

        let h = Poly::<Q>::from_vec(vec![(22, -13), (21, -15), (19, 12), (18, -14), (16, 8), (15, -14), (14, -6),
            (13, 14), (12, -3), (11, 7), (10, -5), (9, -14), (8, 3), (7, 10), (6, 5), (5, -8), (2, 4), (1, 1), (0, 8)]);

        let result = Ring::<P,Q,N>::multiply_poly_mod(Ring::<P,Q,N>::invert_poly(f.clone()), g);

        println!("{:?}\n{:?}", h, result);

        assert!(values_match(h.get_all(), result.get_all()))
    }

    #[test]
    fn test_mods() {
        const Q: i32 = 5;
        assert!(Poly::<Q>::mods(0) == 0);
        assert!(Poly::<Q>::mods(1) == 1);
        assert!(Poly::<Q>::mods(2) == 2);
        assert!(Poly::<Q>::mods(3) == -2);
        assert!(Poly::<Q>::mods(4) == -1);

        const Q2: i32 = 6;
        assert!(Poly::<Q2>::mods(0) == 0);
        assert!(Poly::<Q2>::mods(1) == 1);
        assert!(Poly::<Q2>::mods(2) == 2);
        assert!(Poly::<Q2>::mods(3) == 3);
        assert!(Poly::<Q2>::mods(4) == -2);
        assert!(Poly::<Q2>::mods(5) == -1);
    }

    #[test]
    fn test_ntru() {
        let mut ntru = NTRU::<3, 31, 23>::new();
        ntru.generate_keys();
        let m = Ring::<3, 31, 23>::generate_n_poly();
        let c = match ntru.encrypt(m.clone()) {
            Ok(c) => c,
            Err(error) => panic!("Error: {}", error)
        };
        let mp = match ntru.decrypt(c) {
            Ok(mp) => mp,
            Err(error) => panic!("Error: {}", error)
        };
        
        assert!(values_match(m.values, mp.values));
    }
}
