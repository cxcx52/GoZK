//! Canonical core7 profiles. Membership predicates avoid enumeration of an
//! exponential monomial support. Honest message caps E and actual bounds D
//! are stored separately and cannot be changed after validation.

use crate::Result;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

pub const PROFILE_VERSION: &str = "core7-native-joint9-fresh-v7.1";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ValidatedProfile {
    nu: usize,
    c: usize,
    public_log: usize,
    degree: usize,
    anchor: usize,
    tight: bool,
    flags: u64,
    generic_extras: Option<(BTreeSet<Vec<usize>>, BTreeSet<Vec<usize>>)>,
    l: usize,
    n: usize,
    k: usize,
    n_total: usize,
    e: Vec<usize>,
    d: Vec<usize>,
    source_caps: Vec<usize>,
    native_caps: BTreeMap<String, Vec<usize>>,
    profile_id: String,
}

impl ValidatedProfile {
    /// Flags: bit 0 requests the tight honest profile, bit 1 compiles the public
    /// slice into W, bit 2 enables scalar lookup. Existing core7 0/1 IDs remain
    /// unchanged. Flag 8 selects the projected-mask core7 control with E=D.
    /// Lookup uses E=D until a separate honest-degree proof is given.
    pub fn from_flags(
        nu: usize,
        c: usize,
        public_log: usize,
        degree: usize,
        anchor: Option<usize>,
        flags: u64,
    ) -> Result<Self> {
        Self::new_config(nu, c, public_log, degree, anchor, flags)
    }
    pub fn new_lookup(
        nu: usize,
        c: usize,
        public_log: usize,
        degree: usize,
        anchor: Option<usize>,
        virtual_public: bool,
    ) -> Result<Self> {
        Self::new_config(
            nu,
            c,
            public_log,
            degree,
            anchor,
            4 + 2 * u64::from(virtual_public),
        )
    }
    pub fn new_config(
        nu: usize,
        c: usize,
        public_log: usize,
        degree: usize,
        anchor: Option<usize>,
        flags: u64,
    ) -> Result<Self> {
        let projected = flags == crate::general_mask::PROFILE_FLAG;
        if flags > 7 && !projected {
            return Err("unknown profile flag".into());
        }
        if projected && (nu == 0 || !(1..=4).contains(&c)) {
            return Err("projected-mask core7 requires nu>=1 and 1..=4 column axes".into());
        }
        if flags < 2 && nu > 0 && c > 0 {
            return Self::new(nu, c, public_log, degree, anchor, flags == 1);
        }
        let virtual_public = flags & 2 != 0;
        let lookup = flags & 4 != 0;
        let tight = flags & 1 != 0;
        if degree < 2 || degree > usize::MAX / 4 {
            return Err("degree outside supported range".into());
        }
        if lookup && nu == 0 {
            return Err("lookup requires at least two rows".into());
        }
        if lookup && nu > 21 {
            return Err("lookup cycle certificates support row dimensions through 21".into());
        }
        // New profiles materialize only the small exceptional support, never
        // the dense SRS. Bound this metadata before allocating it from a file.
        if c > 16 || degree > 65536 {
            return Err("exceptional support metadata budget exceeded".into());
        }
        let m = nu.checked_add(c).ok_or("profile dimension overflow")?;
        let ell = m.checked_add(1).ok_or("profile dimension overflow")?;
        let l = if lookup { ell.max(nu + 2) } else { ell };
        if l >= usize::BITS as usize || public_log > m {
            return Err("profile dimension/public slice".into());
        }
        let anchor = anchor.unwrap_or(c);
        if (c == 0 && anchor != 0) || (c > 0 && (anchor == 0 || anchor > c)) {
            return Err("invalid column anchor".into());
        }
        let n = 1usize << nu;
        let k = 1usize << c;
        let offset = l - ell;
        let mut v = BTreeSet::new();
        if projected {
            v = crate::general_mask::support(c, l);
        } else {
            let mut put = |entries: &[(usize, usize)]| {
                let mut a = vec![0; l];
                for (i, e) in entries {
                    a[*i] = *e;
                }
                if a.iter().any(|e| *e > 1) {
                    v.insert(a);
                }
            };
            if c > 0 {
                for column in 0..k {
                    let mut entries = vec![(offset, 2)];
                    for j in 0..c {
                        entries.push((offset + 1 + j, (column >> (c - 1 - j)) & 1));
                    }
                    put(&entries);
                    if lookup {
                        entries[0] = (l - 1, 2);
                        put(&entries);
                    }
                }
                put(&[(offset + anchor, 2)]);
                if !virtual_public {
                    put(&[(offset, 1), (offset + anchor, 2)]);
                }
            } else {
                put(&[(offset, 2)]);
                if nu > 0 {
                    put(&[(l - 1, 2)]);
                }
            }
            if m > 0 {
                for (x, y) in [(2, 0), (0, 2), (1, 2), (2, 1), (2, 2)] {
                    put(&[(offset, x), (l - 1, y)]);
                }
            }
            if lookup {
                for (x, y) in [(2, 0), (0, 2), (1, 2), (2, 1), (2, 2)] {
                    put(&[(l - nu - 2, x), (l - 1, y)]);
                }
                for (x, y) in [(2, 0), (0, 2), (1, 2)] {
                    put(&[(l - nu - 1, x), (l - 1, y)]);
                }
            }
        }
        let source_caps = (0..l)
            .map(|j| v.iter().map(|a| a[j]).max().unwrap_or(1).max(1))
            .collect::<Vec<_>>();
        let mut native_caps = BTreeMap::new();
        let prefix = l - public_log;
        native_caps.insert(
            "gate".into(),
            std::iter::once(offset)
                .chain(l - nu..l)
                .map(|j| degree * (source_caps[j] + usize::from(virtual_public && j < prefix)) + 2)
                .collect::<Vec<_>>(),
        );
        if !virtual_public {
            native_caps.insert(
                "public".into(),
                (offset..l)
                    .map(|j| source_caps[j] + 1 + usize::from(j < prefix))
                    .collect(),
            );
        }
        if m > 0 {
            let leaf = (offset + 1..l)
                .map(|j| source_caps[j] + 1 + usize::from(virtual_public && j < prefix))
                .collect::<Vec<_>>();
            let internal = (offset..l - 1)
                .map(|j| source_caps[j + 1].max(2 * source_caps[j]) + 2)
                .collect::<Vec<_>>();
            native_caps.insert("leaf_A".into(), leaf.clone());
            native_caps.insert("leaf_B".into(), leaf);
            native_caps.insert("internal_A".into(), internal.clone());
            native_caps.insert("internal_B".into(), internal);
            native_caps.insert(
                "root".into(),
                source_caps[offset..].iter().map(|s| s + 1).collect(),
            );
        }
        if lookup {
            native_caps.insert(
                "lookup_left".into(),
                vec![if virtual_public { 4 } else { 3 }; nu + 1],
            );
            native_caps.insert("lookup_right".into(), vec![4; nu + 1]);
            let t = l - nu - 2;
            let internal = (t..l - 1)
                .map(|j| source_caps[j + 1].max(2 * source_caps[j]) + 2)
                .collect::<Vec<_>>();
            native_caps.insert("internal_C".into(), internal.clone());
            native_caps.insert("internal_E".into(), internal);
            native_caps.insert(
                "lookup_root".into(),
                source_caps[t..].iter().map(|s| s + 1).collect(),
            );
        }
        let mut d = vec![0; l];
        for row in native_caps.values() {
            for j in 0..l {
                d[j] = d[j].max(if j < l - row.len() {
                    1
                } else {
                    row[j - (l - row.len())]
                });
            }
        }
        let mut e = d.clone();
        // The core6 honest W has row degree one. Prefix virtualization raises
        // its last row degree only for a one-element public slice.
        if tight && !lookup && nu > 0 && c > 0 {
            e[l - 1] = (degree * (1 + usize::from(virtual_public && public_log == 0)) + 2).max(4);
        }
        let mut u = BTreeSet::new();
        for a in &v {
            for q in quotient_directions(a) {
                if !suffix_multilinear(&q) {
                    u.insert(q);
                }
            }
        }
        // Close the small geometric extras first. Complete pure-power ladders
        // are already quotient closed and must not be expanded quadratically.
        loop {
            let old = u.len();
            let pending = u
                .iter()
                .flat_map(|a| quotient_directions(a))
                .filter(|q| !suffix_multilinear(q))
                .collect::<Vec<_>>();
            u.extend(pending);
            if u.len() == old {
                break;
            }
        }
        let helper_metadata = e
            .iter()
            .try_fold(0usize, |a, b| a.checked_add(*b))
            .ok_or("helper metadata overflow")?;
        if helper_metadata > 1 << 20 {
            return Err("helper support metadata budget exceeded".into());
        }
        for (a, cap) in e.iter().enumerate() {
            for power in 1..=*cap {
                let mut q = vec![0; l];
                q[a] = power;
                if !suffix_multilinear(&q) {
                    u.insert(q);
                }
            }
        }
        let version = if projected {
            "core7-projected-universal-global-v1"
        } else {
            "core-lookup-native-joint9-fresh-v8.1"
        };
        let identity = json!({"version":version,"nu":nu,"c":c,"public_log":public_log,"degree":degree,"anchor":anchor,"flags":flags,"E":e,"D":d,"V_extras":v,"U_extras":u,"layout":"suffix-aligned-native-sources","lookup_function_degree":1});
        let digest = Sha256::digest(serde_json::to_vec(&identity).map_err(|e| e.to_string())?);
        let profile_id = format!("{}:{}", version, hex::encode(digest));
        let profile = Self {
            nu,
            c,
            public_log,
            degree,
            anchor,
            tight,
            flags,
            generic_extras: Some((v, u)),
            l,
            n,
            k,
            n_total: 1usize << m,
            e,
            d,
            source_caps,
            native_caps,
            profile_id,
        };
        profile.checked_counts()?;
        Ok(profile)
    }
    pub fn new(
        nu: usize,
        c: usize,
        public_log: usize,
        degree: usize,
        anchor: Option<usize>,
        tight: bool,
    ) -> Result<Self> {
        if nu == 0 || c == 0 || degree < 2 {
            return Err("profile requires nu,c>=1 and degree>=2".into());
        }
        let m = nu.checked_add(c).ok_or("profile dimension overflow")?;
        let l = m.checked_add(1).ok_or("profile dimension overflow")?;
        if l >= usize::BITS as usize || public_log > m {
            return Err("profile dimension or public slice unsupported".into());
        }
        let anchor = anchor.unwrap_or(c);
        if anchor == 0 || anchor > c {
            return Err("anchor must be a column axis in 1..=c".into());
        }
        if degree
            .checked_mul(2)
            .and_then(|x| x.checked_add(2))
            .is_none()
        {
            return Err("degree overflow".into());
        }
        let source_caps: Vec<usize> = (0..l)
            .map(|i| {
                if i == 0 || i == anchor || i == l - 1 {
                    2
                } else {
                    1
                }
            })
            .collect();
        let mut native_caps: BTreeMap<String, Vec<usize>> = BTreeMap::new();
        native_caps.insert(
            "gate".into(),
            std::iter::once(0)
                .chain(c + 1..l)
                .map(|j| degree * source_caps[j] + 2)
                .collect(),
        );
        native_caps.insert(
            "public".into(),
            source_caps
                .iter()
                .enumerate()
                .map(|(j, s)| s + 1 + usize::from(j < l - public_log))
                .collect(),
        );
        let leaf: Vec<_> = source_caps[1..].iter().map(|s| s + 1).collect();
        let internal: Vec<_> = (0..l - 1)
            .map(|j| source_caps[j + 1].max(2 * source_caps[j]) + 2)
            .collect();
        native_caps.insert("leaf_A".into(), leaf.clone());
        native_caps.insert("leaf_B".into(), leaf);
        native_caps.insert("internal_A".into(), internal.clone());
        native_caps.insert("internal_B".into(), internal);
        native_caps.insert("root".into(), source_caps.iter().map(|s| s + 1).collect());
        let mut d = vec![0; l];
        for row in native_caps.values() {
            for j in 0..l {
                let cap = if j < l - row.len() {
                    1
                } else {
                    row[j - (l - row.len())]
                };
                d[j] = d[j].max(cap);
            }
        }
        let mut e = d.clone();
        if tight {
            e[l - 1] = (degree + 2).max(4);
        }
        let identity = json!({"version":PROFILE_VERSION,"nu":nu,"c":c,"public_log":public_log,
            "degree":degree,"anchor":anchor,"tight":tight,"E":e,"D":d,
            "layout":"Z,columns,rows;suffix-embedded","setup":"fresh-common-G2;fresh-quotient-closed-G1"});
        let digest = Sha256::digest(serde_json::to_vec(&identity).map_err(|e| e.to_string())?);
        let profile_id = format!(
            "{}:{}",
            PROFILE_VERSION,
            digest
                .iter()
                .map(|b| format!("{:02x}", b))
                .collect::<String>()
        );
        let profile = Self {
            nu,
            c,
            public_log,
            degree,
            anchor,
            tight,
            flags: u64::from(tight),
            generic_extras: None,
            l,
            n: 1usize << nu,
            k: 1usize << c,
            n_total: 1usize << m,
            e,
            d,
            source_caps,
            native_caps,
            profile_id,
        };
        // Detect arithmetic overflow in all published counts at construction.
        profile.checked_counts()?;
        Ok(profile)
    }
    fn checked_counts(&self) -> Result<(usize, usize)> {
        if let Some((v, u)) = &self.generic_extras {
            return Ok((
                (1usize << self.l)
                    .checked_add(v.len())
                    .ok_or("V count overflow")?,
                (1usize << (self.l - 1))
                    .checked_add(u.len())
                    .ok_or("U count overflow")?,
            ));
        }
        let sum = self
            .e
            .iter()
            .try_fold(0usize, |a, b| a.checked_add(*b))
            .ok_or("profile cap sum overflow")?;
        let v = (1usize << self.l)
            .checked_add(self.k)
            .and_then(|x| x.checked_add(6))
            .ok_or("V count overflow")?;
        let u = (1usize << (self.l - 1))
            .checked_add(sum - self.l)
            .and_then(|x| x.checked_add(self.k))
            .and_then(|x| x.checked_add(2))
            .ok_or("U count overflow")?;
        Ok((v, u))
    }
    pub fn nu(&self) -> usize {
        self.nu
    }
    pub fn c(&self) -> usize {
        self.c
    }
    pub fn public_log(&self) -> usize {
        self.public_log
    }
    pub fn degree(&self) -> usize {
        self.degree
    }
    pub fn anchor(&self) -> usize {
        self.anchor
    }
    pub fn tight(&self) -> bool {
        self.tight
    }
    pub fn l(&self) -> usize {
        self.l
    }
    pub fn m(&self) -> usize {
        self.nu + self.c
    }
    pub fn ell(&self) -> usize {
        self.nu + self.c + 1
    }
    pub fn core_offset(&self) -> usize {
        self.l - self.ell()
    }
    pub fn flags(&self) -> u64 {
        self.flags
    }
    pub fn virtual_public(&self) -> bool {
        self.flags & 2 != 0
    }
    pub fn lookup(&self) -> bool {
        self.flags & 4 != 0
    }
    pub fn n(&self) -> usize {
        self.n
    }
    pub fn k(&self) -> usize {
        self.k
    }
    pub fn n_total(&self) -> usize {
        self.n_total
    }
    pub fn e(&self) -> &[usize] {
        &self.e
    }
    pub fn d(&self) -> &[usize] {
        &self.d
    }
    pub fn source_caps(&self) -> &[usize] {
        &self.source_caps
    }
    pub fn native_caps(&self) -> &BTreeMap<String, Vec<usize>> {
        &self.native_caps
    }
    pub fn profile_id(&self) -> &str {
        &self.profile_id
    }
    pub fn v_count(&self) -> usize {
        self.checked_counts().expect("validated counts").0
    }
    pub fn u_count(&self) -> usize {
        self.checked_counts().expect("validated counts").1
    }
    pub fn b_v(&self) -> usize {
        if let Some((v, _)) = &self.generic_extras {
            return v
                .iter()
                .map(|a| a.iter().sum())
                .max()
                .unwrap_or(0)
                .max(self.l);
        }
        self.l.max(self.c + 2).max(4)
    }
    pub fn b_u(&self) -> usize {
        if let Some((_, u)) = &self.generic_extras {
            return u
                .iter()
                .map(|a| a.iter().sum())
                .max()
                .unwrap_or(0)
                .max(self.l - 1);
        }
        (self.b_v() - 1).max(*self.e.iter().max().expect("nonempty caps"))
    }
    pub fn delta(&self) -> usize {
        self.b_v().max(self.b_u() + 1)
    }
    pub fn round_scalar_count(&self) -> usize {
        self.e.iter().sum::<usize>() - 1
    }
    pub fn contains_v(&self, a: &[usize]) -> bool {
        if a.len() != self.l {
            return false;
        }
        if a.iter().all(|x| *x <= 1) {
            return true;
        }
        if let Some((v, _)) = &self.generic_extras {
            return v.contains(a);
        }
        if a[0] == 2
            && a[1..=self.c].iter().all(|x| *x <= 1)
            && a[self.c + 1..].iter().all(|x| *x == 0)
        {
            return true;
        }
        if a[1..self.l - 1].iter().all(|x| *x == 0)
            && ((a[self.l - 1] == 2 && a[0] <= 2) || (a[self.l - 1] == 1 && a[0] == 2))
        {
            return true;
        }
        a[0] <= 1 && a[self.anchor] == 2 && (1..self.l).all(|i| i == self.anchor || a[i] == 0)
    }
    pub fn contains_u(&self, a: &[usize]) -> bool {
        if a.len() != self.l {
            return false;
        }
        if a[0] == 0 && a[1..].iter().all(|x| *x <= 1) {
            return true;
        }
        if let Some((_, u)) = &self.generic_extras {
            return u.contains(a);
        }
        let mut nonzero = a.iter().enumerate().filter(|(_, x)| **x != 0);
        if let Some((i, degree)) = nonzero.next() {
            if nonzero.next().is_none() && *degree <= self.e[i] {
                return true;
            }
        }
        if a[0] == 1
            && a[1..=self.c].iter().all(|x| *x <= 1)
            && a[self.c + 1..].iter().all(|x| *x == 0)
        {
            return true;
        }
        a[0] == 1 && a[1..self.l - 1].iter().all(|x| *x == 0) && (1..=2).contains(&a[self.l - 1])
    }
    /// Extras relative to the full L-dimensional multilinear block.
    pub fn v_extras(&self) -> Vec<Vec<usize>> {
        if let Some((v, _)) = &self.generic_extras {
            return v.iter().cloned().collect();
        }
        let mut extras = BTreeSet::new();
        for column in 0..self.k {
            let mut a = vec![0; self.l];
            a[0] = 2;
            for j in 0..self.c {
                a[1 + j] = (column >> (self.c - 1 - j)) & 1;
            }
            extras.insert(a);
        }
        for (z, last) in [(0, 2), (1, 2), (2, 1), (2, 2)] {
            let mut a = vec![0; self.l];
            a[0] = z;
            a[self.l - 1] = last;
            extras.insert(a);
        }
        for z in 0..=1 {
            let mut a = vec![0; self.l];
            a[0] = z;
            a[self.anchor] = 2;
            extras.insert(a);
        }
        extras.into_iter().collect()
    }
    /// Extras relative to the multilinear block on suffix axes 1..L.
    pub fn u_extras(&self) -> Vec<Vec<usize>> {
        if let Some((_, u)) = &self.generic_extras {
            return u.iter().cloned().collect();
        }
        let mut extras = BTreeSet::new();
        for (axis, cap) in self.e.iter().enumerate() {
            for degree in 2..=*cap {
                let mut a = vec![0; self.l];
                a[axis] = degree;
                extras.insert(a);
            }
        }
        for column in 0..self.k {
            let mut a = vec![0; self.l];
            a[0] = 1;
            for j in 0..self.c {
                a[1 + j] = (column >> (self.c - 1 - j)) & 1;
            }
            extras.insert(a);
        }
        for last in 1..=2 {
            let mut a = vec![0; self.l];
            a[0] = 1;
            a[self.l - 1] = last;
            extras.insert(a);
        }
        extras.into_iter().collect()
    }
    /// Conservative shape check for a full embedded multilinear table span.
    pub fn contains_mle_v(&self, start: usize, dimension: usize) -> bool {
        start
            .checked_add(dimension)
            .map_or(false, |end| end <= self.l)
    }
    pub fn contains_mle_u(&self, start: usize, dimension: usize) -> bool {
        if self.generic_extras.is_some() {
            return self.contains_mle_v(start, dimension) && (start >= 1 || dimension == 0);
        }
        self.contains_mle_v(start, dimension) && (start >= 1 || dimension <= self.c + 1)
    }
    /// Explicit support enumeration is a small-test utility, never a setup path.
    pub fn explicit_supports(&self) -> Result<(BTreeSet<Vec<usize>>, BTreeSet<Vec<usize>>)> {
        if self.l > 15 {
            return Err("explicit support enumeration limited to L<=15".into());
        }
        let bits = |i: usize, dim: usize| {
            (0..dim)
                .map(|j| (i >> (dim - 1 - j)) & 1)
                .collect::<Vec<_>>()
        };
        let mut v: BTreeSet<_> = (0..1usize << self.l).map(|i| bits(i, self.l)).collect();
        v.extend(self.v_extras());
        let mut u: BTreeSet<_> = (0..1usize << (self.l - 1))
            .map(|i| {
                let mut a = vec![0];
                a.extend(bits(i, self.l - 1));
                a
            })
            .collect();
        u.extend(self.u_extras());
        Ok((v, u))
    }
}

fn suffix_multilinear(a: &[usize]) -> bool {
    a[0] == 0 && a.iter().all(|e| *e <= 1)
}
fn quotient_directions(a: &[usize]) -> Vec<Vec<usize>> {
    let mut out = vec![];
    for (axis, degree) in a.iter().enumerate() {
        for power in 0..*degree {
            let mut q = vec![0; a.len()];
            q[axis] = power;
            q[axis + 1..].copy_from_slice(&a[axis + 1..]);
            out.push(q);
        }
    }
    out
}
