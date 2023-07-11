use crate::core::*;
use nom::{
    branch::alt,
    bytes::complete::{is_not, tag},
    character::complete::{char, digit1, multispace0, multispace1},
    combinator::{cut, map, map_res, opt},
    multi::fold_many1,
    number::complete::double,
    sequence::{delimited, preceded, terminated},
    IResult,
};

use super::SMTModule;
fn boolean(input: &str) -> IResult<&str, bool> {
    alt((map(tag("true"), |_| true), map(tag("false"), |_| false)))(input)
}
fn decimal(input: &str) -> IResult<&str, usize> {
    map_res(digit1, |r: &str| r.parse())(input)
}
fn float(input: &str) -> IResult<&str, f64> {
    terminated(double, opt(tag("?")))(input)
}
fn real_op(input: &str) -> IResult<&str, f64> {
    let mut count = 0;
    alt((
        preceded(
            terminated(char('*'), multispace1),
            fold_many1(real_val, || 1.0, |acc, i| i * acc),
        ),
        preceded(
            terminated(char('+'), multispace1),
            fold_many1(real_val, || 0.0, |acc, i| i + acc),
        ),
        preceded(
            terminated(char('/'), multispace1),
            fold_many1(
                real_val,
                || f64::NAN,
                |acc, i| {
                    if acc.is_nan() {
                        i
                    } else {
                        acc / i
                    }
                },
            ),
        ),
        preceded(
            terminated(char('-'), multispace1),
            fold_many1(
                real_val,
                || 0.0,
                move |acc, i| {
                    count += 1;
                    let pref = if count == 2 { -1.0 } else { 1.0 };
                    pref * acc - i
                },
            ),
        ),
    ))(input)
}
fn real_val(input: &str) -> IResult<&str, f64> {
    preceded(multispace0, real_expr)(input)
}
fn real_expr(input: &str) -> IResult<&str, f64> {
    alt((
        float,
        delimited(
            char('('),
            preceded(multispace0, real_op),
            cut(preceded(multispace0, char(')'))),
        ),
    ))(input)
}
fn string(input: &str) -> IResult<&str, &str> {
    delimited(char('"'), is_not("\""), char('"'))(input)
}
fn variable(input: &str) -> IResult<&str, usize> {
    map(preceded(char('v'), decimal), |r| r)(input)
}
struct ValueParser<F> {
    var_ty: F,
}
impl<F> ValueParser<F>
where
    F: Fn(usize) -> Type,
{
    fn inner<'a>(&self, i: &'a str) -> IResult<&'a str, (usize, ConfigValue)> {
        let (i, var) = preceded(multispace0, variable)(i)?;
        match (self.var_ty)(var) {
            Type::Bool => map(preceded(multispace1, boolean), |b| ConfigValue::Bool(b))(i),
            Type::Real => map(preceded(multispace1, real_expr), |b| ConfigValue::Number(b))(i),
            Type::String => map(preceded(multispace1, string), |b| {
                ConfigValue::String(b.to_string())
            })(i),
            _ => unimplemented!(),
        }
        .map(|(s, v)| (s, (var, v)))
    }
    fn parse<'a>(&self, i: &'a str) -> IResult<&'a str, (usize, ConfigValue)> {
        preceded(
            multispace0,
            delimited(
                char('('),
                |i| self.inner(i),
                cut(preceded(multispace0, char(')'))),
            ),
        )(i)
    }
}

pub fn iter_values<'a>(
    smt_module: &'a SMTModule,
    module: &'a Module,
    mut values: &'a str,
) -> impl Iterator<Item = (ModuleSymbol, ConfigValue)> + 'a {

    values = &values[values.find('(').map(|i|i+1).unwrap_or(0) ..];
    let parser = ValueParser {
        var_ty: |id| module.type_of(smt_module.variables[id]),
    };
    std::iter::from_fn(move || match parser.parse(values) {
        Ok((i, (v, c))) => {
            values = i;
            Some((smt_module.variables[v], c))
        }
        Err(_e) =>{
            None

        },
    })
}

#[cfg(test)]
mod tests {
    #[macro_export]
    macro_rules! assert_approx_eq {
        ($a:expr, $b:expr) => {{
            let eps = 1.0e-6;
            let (a, b) = (&$a, &$b);
            assert!(
                (*a - *b).abs() < eps,
                "assertion failed: `(left !== right)` \
             (left: `{:?}`, right: `{:?}`, expect diff: `{:?}`, real diff: `{:?}`)",
                *a,
                *b,
                eps,
                (*a - *b).abs()
            );
        }};
        ($a:expr, $b:expr, $eps:expr) => {{
            let (a, b) = (&$a, &$b);
            let eps = $eps;
            assert!(
                (*a - *b).abs() < eps,
                "assertion failed: `(left !== right)` \
             (left: `{:?}`, right: `{:?}`, expect diff: `{:?}`, real diff: `{:?}`)",
                *a,
                *b,
                eps,
                (*a - *b).abs()
            );
        }};
    }
    use super::*;
    #[test]
    fn test_values() {
        let i = "(v0 (- 1.0))
         (v1 (- (/ 1.0 103.0) ))
         (v2 (- 100 (/ 1.333? 102.000)  ))
            (v3 \"test\")
            (v4 true  )
            (v5 1.0)
            ( v6 10)
         )";
        let parser = ValueParser {
            var_ty: |i: usize| match i {
                3 => Type::String,
                4 => Type::Bool,
                _ => Type::Real,
            },
        };
        let (i,(_,ConfigValue::Number(n))) = parser.parse(i).unwrap() else {panic!()};
        assert_approx_eq!(n, -1.0);
        let (i,(_,ConfigValue::Number(n))) = parser.parse(i).unwrap() else {panic!()};
        assert_approx_eq!(n, -1.0 / 103.0);
        let (i,(_,ConfigValue::Number(n))) = parser.parse(i).unwrap() else {panic!()};
        assert_approx_eq!(n, 100.0 - 1.333 / 102.0);
        let (i,(_,ConfigValue::String(n))) = parser.parse(i).unwrap() else {panic!()};
        assert_eq!(n, "test");
        let (i,(_,ConfigValue::Bool(n))) = parser.parse(i).unwrap() else {panic!()};
        assert_eq!(n, true);
        let (_i,(_,ConfigValue::Number(n))) = parser.parse(i).unwrap() else {panic!()};
        assert_approx_eq!(n,1.0);
    }
}
