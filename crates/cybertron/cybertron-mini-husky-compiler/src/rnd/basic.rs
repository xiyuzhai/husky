use husky_rng_utils::XRng;
use serde::de::value;
use serde::ser::{SerializeSeq, Serializer};
use serde::{Deserialize, Serialize};

pub fn rnd_codes(
    n: u64,
    max_fns: usize,
    min_dist: usize,
    use_var_rate: f64,
    error_rate: f64,
) -> Vec<(Vec<String>, Vec<TokenInfo>)> {
    let mut data = Vec::new();

    for seed in 0..n {
        data.push(rnd_code(seed, max_fns, min_dist, use_var_rate, error_rate));
    }
    data
}

#[derive(Serialize, Clone, Copy, Debug)]
pub struct TokenInfo {
    #[serde(serialize_with = "serialize_option_ast_kind")]
    ast_kind: Option<AstKind>,
    #[serde(serialize_with = "serialize_option_symbol_resolution")]
    symbol_resolution: Option<SymbolResolution>,
    // #[serde(serialize_with = "serialize_option_type_error")]
    // error: Option<TypeError>,
    #[serde(serialize_with = "serialize_option_type")]
    expected_type: Option<Type>,
    #[serde(serialize_with = "serialize_option_type")]
    actual_type: Option<Type>,
}

#[derive(Serialize, Clone, Copy, Debug)]
pub enum AstKind {
    FnEntityName = 1,
    ParameterType = 2,
    ParameterIdent = 3,
    FnEntityUsage = 4,
    CallLpar = 5,
    FnKeyword = 6,
    LetKeyword = 7,
    CallRpar = 8,
    IntLiteral = 9,
    FloatLiteral = 10,
    BoolLiteral = 11,
    ParametersLpar = 12,
    ParametersRpar = 13,
    FnBodyLcurl = 14,
    FnBodyRcurl = 15,
    ParameterTypeColon = 16,
    StmtColon = 17,
}

#[derive(Serialize, Clone, Copy, Debug)]
pub enum SymbolResolution {
    Fn = 1,
    Unresolved = 2,
}

#[derive(Serialize, Clone, Copy, Debug)]
pub enum TypeError {
    Expected = 1,
}

pub fn rnd_code(
    seed: u64,
    max_fns: usize,
    min_dist: usize,
    use_var_rate: f64,
    error_rate: f64,
) -> (Vec<String>, Vec<TokenInfo>) {
    let mut bcg = BasicCodeGenerator::new(seed, min_dist, use_var_rate, error_rate);
    bcg.gen_fns(max_fns);
    bcg.finish()
}

struct BasicCodeGenerator {
    rng: XRng,
    functions: Vec<Function>,
    result: Vec<String>,
    token_infos: Vec<TokenInfo>,
    min_dist: usize,
    use_var_rate: f64,
    error_rate: f64,
    max_calls_per_fn: usize,
    used_fn_idx: Vec<usize>,
    int_literals: Vec<String>,
    float_literals: Vec<String>,
    bool_literals: Vec<String>,
    var_name_literals: Vec<String>,
    time_step: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Type {
    Bool,
    Int,
    Float,
}

impl Type {
    fn repr(self) -> &'static str {
        match self {
            Type::Bool => "Bool",
            Type::Int => "Int",
            Type::Float => "Float",
        }
    }
}

struct Function {
    name: String,
    input_ty: Type,
    last_called_step: usize,
}

impl BasicCodeGenerator {
    fn new(seed: u64, min_dist: usize, use_var_rate: f64, error_rate: f64) -> Self {
        let mut int_literals: Vec<String> = Vec::new();
        for i in 0..99 {
            int_literals.push(i.to_string());
        }

        let mut float_literals: Vec<String> = Vec::new();
        for i in 0..99 {
            float_literals.push(format!("{i}.1"));
        }

        let bool_literals = vec!["true".to_string(), "false".to_string()];

        let mut var_name_literals: Vec<String> = Vec::new();
        for i in 0..26 {
            var_name_literals.push(format!("{}", (b'a' + i) as char));
        }

        Self {
            rng: XRng::new(seed),
            functions: Default::default(),
            result: Vec::new(),
            token_infos: Vec::new(),
            min_dist,
            use_var_rate,
            error_rate,
            max_calls_per_fn: 10,
            used_fn_idx: Vec::new(),
            int_literals,
            float_literals,
            bool_literals,
            var_name_literals,
            time_step: 0,
        }
    }

    fn push_token(
        &mut self,
        token: impl Into<String>,
        ast_kind: Option<AstKind>,
        symbol_resolution: Option<SymbolResolution>,
        expected_type: Option<Type>,
        actual_type: Option<Type>,
    ) {
        self.result.push(token.into());
        self.token_infos.push(TokenInfo {
            ast_kind,
            symbol_resolution,
            expected_type,
            actual_type,
        });
    }

    fn with_curly(&mut self, lcurl_kind: AstKind, rcurl_kind: AstKind, f: impl FnOnce(&mut Self)) {
        self.push_token("{", Some(lcurl_kind), None, None, None);
        f(self);
        self.push_token("}", Some(rcurl_kind), None, None, None);
    }

    fn gen_fn(&mut self) {
        let mut fn_idx = self.rng.rand_range(0..100);
        while self.used_fn_idx.contains(&fn_idx) {
            fn_idx = self.rng.rand_range(0..100);
        }
        self.used_fn_idx.push(fn_idx);
        let fn_name = format!("f{fn_idx}");
        let input_ty = match self.rng.rand_range(0..3) {
            0 => Type::Bool,
            1 => Type::Int,
            2 => Type::Float,
            _ => unreachable!(),
        };
        let var_name =
            self.var_name_literals[self.rng.rand_range(0..self.var_name_literals.len())].clone();

        self.push_token("fn", Some(AstKind::FnKeyword), None, None, None);
        self.push_token(
            fn_name.clone(),
            Some(AstKind::FnEntityName),
            Some(SymbolResolution::Fn),
            None,
            None,
        );
        self.push_token("(", Some(AstKind::ParametersLpar), None, None, None);
        self.push_token(
            var_name.clone(),
            Some(AstKind::ParameterIdent),
            None,
            Some(input_ty),
            Some(input_ty),
        );
        self.push_token(":", Some(AstKind::ParameterTypeColon), None, None, None);
        self.push_token(
            input_ty.repr(),
            Some(AstKind::ParameterType),
            None,
            Some(input_ty), // None,
            Some(input_ty), // None,
        );
        self.push_token(")", Some(AstKind::ParametersRpar), None, None, None);
        self.with_curly(AstKind::FnBodyLcurl, AstKind::FnBodyRcurl, |gen| {
            for _ in 0..gen.max_calls_per_fn {
                gen.gen_fn_call(var_name.clone(), Some(input_ty));
            }
        });
        self.functions.push(Function {
            name: fn_name,
            input_ty: input_ty,
            last_called_step: self.time_step,
        });
        self.time_step += 1;
    }

    fn gen_fn_call(&mut self, var_name: String, var_type: Option<Type>) {
        let len = self.functions.len();
        if len == 0 {
            return;
        }

        let callee_index = self.rng.rand_range(0..len);
        let callee = &mut self.functions[callee_index];

        if self.time_step - callee.last_called_step < self.min_dist {
            return;
        }

        callee.last_called_step = self.time_step;
        let fn_name = callee.name.clone();
        let expected_type = callee.input_ty.clone();
        let mut value_type = expected_type.clone();

        let mut arg_literal = String::new();
        let mut literal_kind = AstKind::IntLiteral;

        let use_var = self.rng.randf64() < self.use_var_rate;
        if use_var {
            arg_literal = var_name.clone();
            literal_kind = AstKind::ParameterIdent;
            value_type = var_type.unwrap();
        } else {
            let has_ty_error = self.rng.randf64() < self.error_rate;

            value_type = if has_ty_error {
                let mut types = vec![Type::Bool, Type::Int, Type::Float];
                types.retain(|&x| x != expected_type);
                types[self.rng.rand_range(0..types.len())].clone()
            } else {
                expected_type
            };

            (arg_literal, literal_kind) = {
                match value_type {
                    Type::Bool => (
                        self.bool_literals[self.rng.rand_range(0..self.bool_literals.len())]
                            .clone(),
                        AstKind::BoolLiteral,
                    ),
                    Type::Int => (
                        self.int_literals[self.rng.rand_range(0..self.int_literals.len())].clone(),
                        AstKind::IntLiteral,
                    ),
                    Type::Float => (
                        self.float_literals[self.rng.rand_range(0..self.float_literals.len())]
                            .clone(),
                        AstKind::FloatLiteral,
                    ),
                }
            };
        }

        self.push_token(
            fn_name,
            Some(AstKind::FnEntityUsage),
            Some(SymbolResolution::Fn),
            None,
            None,
        );
        self.push_token("(", Some(AstKind::CallLpar), None, None, None);
        self.push_token(
            arg_literal,
            Some(literal_kind),
            None,
            Some(expected_type),
            Some(value_type),
        );
        self.push_token(")", Some(AstKind::CallRpar), None, None, None);
        self.push_token(";", Some(AstKind::StmtColon), None, None, None);
    }

    fn gen_fns(&mut self, max_fns: usize) {
        let num_fns = self.rng.rand_range(3..=max_fns.max(3));
        for _ in 0..num_fns {
            self.gen_fn()
        }
    }

    fn finish(self) -> (Vec<String>, Vec<TokenInfo>) {
        (self.result, self.token_infos)
    }
}

fn serialize_option_ast_kind<S>(value: &Option<AstKind>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match value {
        None => serializer.serialize_u8(0),
        Some(kind) => serializer.serialize_u8(*kind as u8),
    }
}

fn serialize_option_symbol_resolution<S>(
    value: &Option<SymbolResolution>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match value {
        None => serializer.serialize_u8(0),
        Some(resolution) => serializer.serialize_u8(*resolution as u8),
    }
}

fn serialize_option_type_error<S>(
    value: &Option<TypeError>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match value {
        None => serializer.serialize_u8(0),
        Some(TypeError::Expected) => serializer.serialize_u8(1),
    }
}

fn serialize_option_type<S>(value: &Option<Type>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match value {
        None => serializer.serialize_u8(0),
        Some(Type::Bool) => serializer.serialize_u8(1),
        Some(Type::Int) => serializer.serialize_u8(2),
        Some(Type::Float) => serializer.serialize_u8(3),
    }
}
