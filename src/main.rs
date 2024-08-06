use egg::{rewrite as rw, *};
use num::Zero;
pub type EGraph = egg::EGraph<Math, ConstantFold>;
pub type Rewrite = egg::Rewrite<Math, ConstantFold>;
pub type Num = num::Rational32;
pub type Constant = Num;
define_language! {
    pub enum Math {
        Num(Num),
        "d" = Diff([Id; 2]),
        "i" = Integral([Id; 2]),

        "+" = Add([Id; 2]),
        "-" = Sub([Id; 2]),
        "*" = Mul([Id; 2]),
        "/" = Div([Id; 2]),
        "^" = Pow([Id; 2]),
        "ln" = Ln(Id),
        "sqrt" = Sqrt(Id),

        "sin" = Sin(Id),
        "cos" = Cos(Id),
        "tan" = Tan(Id),
        "sinh" = Sinh(Id),
        "cosh" = Cosh(Id),
        "tanh" = Tanh(Id),
        "subst" = Subst([Id; 3]),
        "exp" = Exp([Id; 1]),

        "erf" = Erf([Id;1]),

        "pi" = Pi,

        Constant(Constant),
        Var(Symbol),
    }
}

// You could use egg::AstSize, but this is useful for debugging, since
// it will really try to get rid of the Diff operator
pub struct MathCostFn;
impl egg::CostFunction<Math> for MathCostFn {
    type Cost = usize;
    fn cost<C>(&mut self, enode: &Math, mut costs: C) -> Self::Cost
    where
        C: FnMut(Id) -> Self::Cost,
    {
        let op_cost = match enode {
            Math::Diff(..) => 1000,
            Math::Integral(..) => 1000,
            _ => 1,
        };
        enode.fold(op_cost, |sum, i| sum + costs(i))
    }
}

#[derive(Default)]
pub struct ConstantFold;
impl Analysis<Math> for ConstantFold {
    type Data = Option<(Constant, PatternAst<Math>)>;

    fn make(egraph: &egg::EGraph<Math, ConstantFold>, enode: &Math) -> Self::Data {
        let get = |id: &Id| egraph[*id].data.as_ref();
        Some(match enode {
            Math::Num(n) => (n.clone(), format!("{}", n).parse().unwrap()),
            Math::Constant(c) => (c.clone(), format!("{}", c).parse().unwrap()),
            Math::Add([a, b]) => (
                get(a)?.0.clone() + get(b)?.0.clone(),
                format!("(+ {} {})", get(a)?.0, get(b)?.0).parse().unwrap(),
            ),
            Math::Sub([a, b]) => (
                get(a)?.0.clone() - get(b)?.0.clone(),
                format!("(- {} {})", get(a)?.0, get(b)?.0).parse().unwrap(),
            ),
            Math::Mul([a, b]) => (
                get(a)?.0.clone() * get(b)?.0.clone(),
                format!("(* {} {})", get(a)?.0, get(b)?.0).parse().unwrap(),
            ),
            Math::Div([a, b]) if get(b)?.0 != Num::zero() => (
                get(a)?.0.clone() / get(b)?.0.clone(),
                format!("(/ {} {})", get(a)?.0, get(b)?.0).parse().unwrap(),
            ),
            _ => return None,
        })
    }

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        merge_option(to, from, |a, b| {
            assert_eq!(a.0, b.0, "Merged non-equal constants");
            DidMerge(false, false)
        })
    }

    fn modify(egraph: &mut EGraph, id: Id) {
        let data = egraph[id].data.clone();
        if let Some((c, pat)) = data {
            if egraph.are_explanations_enabled() {
                egraph.union_instantiations(
                    &pat,
                    &format!("{}", c).parse().unwrap(),
                    &Default::default(),
                    "constant_fold".to_string(),
                );
            } else {
                let added = egraph.add(Math::Constant(c));
                egraph.union(id, added);
            }
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}
///
///
/// in mathematica, it's FreeQ[{a,b,c,d...}, x]
/// in rust, it's freeq(["?a", "?b", "?c", ...], "?x")
///
fn freeq<'a>(v: &'a [&'a str], w: &'a str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool + 'a {
    let w = w.parse().unwrap();
    move |egraph, _, subst| {
        v.iter().all(|v| {
            let v = v.parse().unwrap();
            egraph.find(subst[v]) != egraph.find(subst[w])
                && (egraph[subst[v]].data.is_some()
                    || egraph[subst[v]]
                        .nodes
                        .iter()
                        .any(|n| matches!(n, Math::Var(..))))
        })
    }
}

fn is_const(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| egraph[subst[var]].data.is_some()
}
fn is_sym(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        egraph[subst[var]]
            .nodes
            .iter()
            .any(|n| matches!(n, Math::Var(..)))
    }
}

fn is_not_zero(var: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    return pred1(var, |x| x != 0.into());
}

fn pred1(p: &str, pred: impl Fn(Num) -> bool) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let p = p.parse().unwrap();
    move |egraph, _, subst| {
        if let &Some((p, _)) = &egraph[subst[p]].data {
            return pred(p);
        } else {
            true
        }
    }
}

fn pred2(
    m: &str,
    n: &str,
    pred: impl Fn(Num, Num) -> bool,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let m = m.parse().unwrap();
    let n = n.parse().unwrap();
    move |egraph, _, subst| {
        if let (&Some((m, _)), &Some((n, _))) = (&egraph[subst[m]].data, &egraph[subst[n]].data) {
            return pred(m, n);
        } else {
            true
        }
    }
}
fn pred3(
    a: &str,
    b: &str,
    c: &str,
    pred: impl Fn(Num, Num, Num) -> bool,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let a = a.parse().unwrap();
    let b = b.parse().unwrap();
    let c = c.parse().unwrap();
    move |egraph, _, subst| {
        if let (&Some((a, _)), &Some((b, _)), &Some((c, _))) = (
            &egraph[subst[a]].data,
            &egraph[subst[b]].data,
            &egraph[subst[c]].data,
        ) {
            return pred(a, b, c);
        } else {
            true
        }
    }
}

fn pred4(
    a: &str,
    b: &str,
    c: &str,
    d: &str,
    pred: impl Fn(Num, Num, Num, Num) -> bool,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let a = a.parse().unwrap();
    let b = b.parse().unwrap();
    let c = c.parse().unwrap();
    let d = d.parse().unwrap();
    move |egraph, _, subst| {
        if let (&Some((a, _)), &Some((b, _)), &Some((c, _)), &Some((d, _))) = (
            &egraph[subst[a]].data,
            &egraph[subst[b]].data,
            &egraph[subst[c]].data,
            &egraph[subst[d]].data,
        ) {
            return pred(a, b, c, d);
        } else {
            true
        }
    }
}

fn pred5(
    a: &str,
    b: &str,
    c: &str,
    d: &str,
    e: &str,
    pred: impl Fn(Num, Num, Num, Num, Num) -> bool,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let a = a.parse().unwrap();
    let b = b.parse().unwrap();
    let c = c.parse().unwrap();
    let d = d.parse().unwrap();
    let e = e.parse().unwrap();
    move |egraph, _, subst| {
        if let (&Some((a, _)), &Some((b, _)), &Some((c, _)), &Some((d, _)), &Some((e, _))) = (
            &egraph[subst[a]].data,
            &egraph[subst[b]].data,
            &egraph[subst[c]].data,
            &egraph[subst[d]].data,
            &egraph[subst[e]].data,
        ) {
            return pred(a, b, c, d, e);
        } else {
            true
        }
    }
}
fn pred6(
    a: &str,
    b: &str,
    c: &str,
    d: &str,
    e: &str,
    f: &str,
    pred: impl Fn(Num, Num, Num, Num, Num, Num) -> bool,
) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let a = a.parse().unwrap();
    let b = b.parse().unwrap();
    let c = c.parse().unwrap();
    let d = d.parse().unwrap();
    let e = e.parse().unwrap();
    let f = f.parse().unwrap();
    move |egraph, _, subst| {
        if let (
            &Some((a, _)),
            &Some((b, _)),
            &Some((c, _)),
            &Some((d, _)),
            &Some((e, _)),
            &Some((f, _)),
        ) = (
            &egraph[subst[a]].data,
            &egraph[subst[b]].data,
            &egraph[subst[c]].data,
            &egraph[subst[d]].data,
            &egraph[subst[e]].data,
            &egraph[subst[f]].data,
        ) {
            return pred(a, b, c, d, e, f);
        } else {
            true
        }
    }
}
fn Power(x: Num, n: i32) -> Num {
    x.pow(n)
}

#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> {
        include!("../rule.in")
    }

#[cfg(test)]
mod test {
    use std::ops::Not;

    use super::*;
    #[test]
    fn test_int() {
        let rules = rules();
        for start in [
            //"(+ (* a (sin x)) (^ x m))", "(/ 5 x)",
            //"(* (^ (* 9   (cos (+ eee   (* f   x))))   n)   (^ (* 6   (sin (+ eee   (* f   x))))   m))",
            //"(^ (+ a (* b x)) 5)",
            //"a",
            //"(* x 4)",
            "(* (exp x) (^ x 3))", //"(/ x (+ a (* b x)))"
        ]
        .map(|x| format!("(i {x} x)"))
        {
            let start = start.parse().unwrap();
            let mut runner = Runner::default()
                .with_explanations_enabled()
                .with_expr(&start)
                .with_node_limit(60000)
                .run(&rules);
            let extractor = Extractor::new(&runner.egraph, MathCostFn);
            let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);
            assert!(&best_expr.to_string().contains("(i").not());
            dbg!(best_expr.to_string());
            dbg!(runner
                .explain_equivalence(&start, &best_expr)
                .get_flat_strings());
        }
    }
}

fn main() {
    println!("hello world");
}
