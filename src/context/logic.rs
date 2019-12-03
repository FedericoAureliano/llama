use std::fmt;

pub struct Logic {
    pub q: bool,
    pub lia: bool,
    pub uf: bool,
}

impl Logic {
    pub fn new() -> Logic {
        let l = Logic {
            q: false,
            lia: false,
            uf: false,
        };
        l
    }
    pub fn to_logic(s: &str) -> Logic {
        match s {
            "QF_UF" => Logic {
                q: false,
                lia: false,
                uf: true,
            },
            "QF_LIA" => Logic {
                q: false,
                lia: true,
                uf: false,
            },
            "QF_UFLIA" => Logic {
                q: false,
                lia: true,
                uf: true,
            },
            _ => panic!(format!("logic {} not supported", s))
        }
    }
}

impl fmt::Display for Logic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let q = if self.q {panic!("quantified variables not supported yet")} else {"QF_"};
        let uf = if self.uf {"UF"} else {""};
        let lia = if self.lia {"LIA"} else {""};
        write!(f, "{}{}{}", q, uf, lia)
    }
}