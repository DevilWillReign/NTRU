pub mod poly {
    use std::{collections::{BTreeMap, btree_map::Keys}, fmt::Display, borrow::BorrowMut};

    use itertools::Itertools;


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

        pub fn poly_invertible(&self) -> bool {
            let mut v = 0;
            for val in self.values.values() {
                v += val;
            }
            v != 0
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
                nmap.insert(*k, Self::find_coeff(*v, s));
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

        pub fn keys(&self) -> Keys<i64, i64> {
            return self.values.keys();
        }

        pub fn get_all(&self) -> BTreeMap<i64, i64> {
            return self.values.clone();
        }

        pub fn mods(a: i64) -> i64 {
            return Self::mods_2p(a, Q);
        }

        fn mods_2p(a: i64, n: i64) -> i64 {
            return (a + (n-1)/2).rem_euclid(n) - (n-1)/2
        }

        pub fn add(&self, p: &Self) -> Self {
            let mut nmap = Self::new();
            let mut iter1 = self.values.keys().map(|k| *k).into_iter().collect::<Vec<i64>>();
            iter1.append(p.values.keys().map(|k| *k).into_iter().collect::<Vec<i64>>().borrow_mut());
            let indexes = iter1.into_iter().unique().collect::<Vec<i64>>();
            
            for i in indexes {
                nmap.insert(i, self.get(i) + p.get(i));
            }

            return nmap;
        }

        pub fn sub(&self, p: &Self) -> Self {
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

        pub fn multiply_poly(&self, poly2: &Self) -> Self {
            let mut poly3 = Self::new();
            for i in self.values.keys() {
                for j in poly2.values.keys() {
                    poly3.insert(*i+*j, poly3.get(*i+*j) + self.get(*i) * poly2.get(*j));
                }
            }
            return poly3;
        }

        pub fn inverse_int(a: i64) -> (i64, i64) {
            let mut t = 0;
            let mut newt = 1;
            let mut r = Q;
            let mut newr = a;

            while newr != 0 {
                let quotient = (r - Self::mods_2p(r, newr)) / newr;
                (t, newt) = (newt, t - quotient * newt);
                (r, newr) = (newr, r - quotient * newr);
            }
            // if r > 1 {
            //     println!("r: {}, gcd(a,Q): {}", r, Self::gcd(a, Q));
            //     panic!("Cannot inverse");
            // }

            if t < 0 {
                t += Q;
            }
            // println!("r mods Q: {}, a: {}, t: {}", Self::mods(r), a, Self::mods(r*t*a));
            return (t, r)
        }

        pub fn gcd(v: i64, n: i64) -> i64 {
            let mut a = v;
            let mut b = n; 
            
            while b != 0 {
                let t = b;
                b = Self::mods_2p(a,b);
                a = t;
            }
            return a
        }

        pub fn find_coeff(div_coeff: i64, inv_coeff: i64) -> i64 {
            // let now = Instant::now();
            let (inv, r) = Self::inverse_int(inv_coeff);
            // let c = Self::mods((inv*div_coeff) / Self::gcd(inv_coeff, Q));
            // println!("div_coeff: {}, c: {}", div_coeff, c);
            // if r != 1 {
            //     let (invr, rr) = Self::inverse_int(r);
            //     println!("{} {}, {} {}, {}", r, div_coeff, invr, rr, (inv*div_coeff) / r);
            //     return (inv*div_coeff) * Self::inverse_int(r).0;
            // }
            // let elapsed_time = now.elapsed();
            // println!("Running inverse_int() took {} seconds.", elapsed_time.as_nanos());
            // let now = Instant::now();
            // let mut i = 1;
            // while 1 != Self::mods(i * inv_coeff) {
            //     i += 1;
            // }
            // let elapsed_time = now.elapsed();
            // println!("Running while took {} seconds.", elapsed_time.as_nanos());
            // println!("inv: {}, i: {}", inv, i);
            return (inv * div_coeff) / r;
            // return i * div_coeff;
        }

        pub fn division_poly(p1: &Self, p2: &Self) -> (Self, Self) {
            let mut r = p1.clone();
            let mut quotient = Self::new();
            let p2d = p2.deg();
            let p2v = p2.get(p2d);

            while r.deg() >= p2d && r != Self::new() {
                let vv = Self::find_coeff(r.get(r.deg()), p2v);
                let v = Self::from_vec(vec![(r.deg()-p2d, vv)]);
                r = r.sub(&v.multiply_poly(&p2));
                quotient = quotient.add(&v);
            }
            return (quotient, r)
        }

        pub fn extended_poly_gcd(a: &Self, b: &Self) -> (Self, Self, Self) {
            let mut old_s = Self::from_vec(vec![(0, 1)]);
            let mut old_r = a.clone();
            let mut s = Self::new();
            let mut r = b.clone();
            
            while r != Self::new() {
                let (quotient,remainder) = Self::division_poly(&old_r, &r);
                (old_r, r) = (r.clone(), remainder);
                (old_s, s) = (s.clone(), old_s.sub(&quotient.multiply_poly(&s)));
            }

            old_s = old_s.div_scalar(old_r.get(old_r.deg()));

            return (old_r.clone(), old_s.clone(), Self::division_poly(&old_r.sub(&old_s.multiply_poly(&a)), &b).0)
        }

        pub fn invert_poly(poly1: &Self, n: &Self) -> Self {
            let mut t = Self::new();
            let mut newt = Self::from_vec(vec![(0, 1)]);
            let mut r = n.clone();
            let mut newr = poly1.clone();

            while newr != Self::new() {
                let (quotient,remainder) = Self::division_poly(&r, &newr);
                (r, newr) = (newr.clone(), remainder);
                (t, newt) = (newt.clone(), t.sub(&quotient.multiply_poly(&newt)));
            }
            return t.div_scalar(r.get(r.deg()));
        }
    }
}