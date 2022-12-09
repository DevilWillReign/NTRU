extern crate rand;

use rand::{thread_rng, Rng};
use rand::distributions::Uniform;

use std::collections::HashMap;

pub struct Keys {
    pub_key: Poly,
    priv_key: Poly,
}

pub struct Poly {
    values: HashMap<i128, i128>,
}

impl Clone for Poly {
    
    fn clone(&self) -> Self {
        Poly::from(self.values.clone())
    }
}

impl Poly {

    pub fn new() -> Self {
        Self { values: HashMap::new() }
    }

    pub fn from(values: HashMap<i128, i128>) -> Self {
        Self { values: values }
    }

    pub fn mul_scalar(&self, s: i128) -> Poly {
        let mut nmap = HashMap::new();
        for (k, v) in self.values.iter() {
            nmap.insert(*k, v * s);
        }
        return Poly::from(nmap);
    }
    
    pub fn insert(&mut self, k: i128, v: i128) {
        if v != 0 {
            self.values.insert(k, v);
        }
    }

    pub fn get(&self, k: i128) -> i128 {
        return match self.values.get(&k) {
            Some(v) => *v,
            None => 0,
        }
    }
}

pub fn invert_poly(p: Poly, n: i128) -> Poly {
    let mut inv = Poly::new();
    return inv
}

pub fn generate_keys(p: i128, q: i128, n: i128) -> Keys {
    let G = generate_n_poly(n);
    let F = generate_n_poly(n);
    let mut f = F.mul_scalar(p);
    f.insert(0, f.get(0) + 1);
    let g = G.mul_scalar(p);
    let h = multiply_poly(invert_poly(f.clone(), n), g, n); 
    return Keys { pub_key: f, priv_key: h }
}

pub fn generate_n_poly(n: i128) -> Poly {
    let mut p = Poly::new();
    let mut rng = thread_rng();
    let side = Uniform::new_inclusive(-1, 1);
    for i in 0..n {
        p.insert(i, rng.sample(side));
    }
    return p;
}

pub fn multiply_poly(poly1: Poly, poly2: Poly, n: i128) -> Poly {
    let mut poly3 = Poly::new();
    for i in 0..n {
        let mut v = 0;
        for j in 0..n {
            v += poly1.get(j) * poly2.get((i - j).rem_euclid(n));
        }
        poly3.insert(i, v);
    }
    return poly3;
}

#[cfg(test)]
mod tests {
    use super::*;

    impl Poly {
        pub fn get_all(&self) -> HashMap<i128, i128> {
            return self.values.clone();
        }
    }

    fn values_match(values1: HashMap<i128, i128>, values2: HashMap<i128, i128>) -> bool {
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
        let N = 3;

        let mut p1 = Poly::new();
        p1.insert(2, 1);
        p1.insert(1, 3);
        p1.insert(0, 1);

        let mut p2 = Poly::new();
        p2.insert(2, 2);
        p2.insert(1, 1);
        p2.insert(0, -4);


        let mut p3 = Poly::new();
        p3.insert(2, 1);
        p3.insert(1, -9);
        p3.insert(0, 3);
        
        assert!(values_match(multiply_poly(p1, p2, 3).get_all(), p3.get_all()))
    }

    #[test]
    fn generate_n_poly_test() {
        let p1 = generate_n_poly(10);

        let p2 = generate_n_poly(10);

        assert!(!values_match(p1.get_all(), p2.get_all()))
    }
}
