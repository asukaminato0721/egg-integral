use std::ops::Sub;

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

fn freeq(v: &str, w: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let v = v.parse().unwrap();
    let w = w.parse().unwrap();
    move |egraph, _, subst| {
        egraph.find(subst[v]) != egraph.find(subst[w])
            && (egraph[subst[v]].data.is_some()
                || egraph[subst[v]]
                    .nodes
                    .iter()
                    .any(|n| matches!(n, Math::Var(..))))
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
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(n) = &egraph[subst[var]].data {
            (n.0) != Default::default()
        } else {
            true
        }
    }
}

fn neq(var: &str, val: Num) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let var = var.parse().unwrap();
    move |egraph, _, subst| {
        if let Some(n) = &egraph[subst[var]].data {
            n.0 != val
        } else {
            true
        }
    }
}

fn b2_4ac(b: &str, a: &str, c: &str, val: Num) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let a = a.parse().unwrap();
    let b = b.parse().unwrap();
    let c = c.parse().unwrap();
    move |egraph, _, subst| {
        let a = &egraph[subst[a]].data.clone().expect("find a").0;
        let b = &egraph[subst[b]].data.clone().unwrap().0;
        let c = &egraph[subst[c]].data.clone().unwrap().0;
        return b
            .pow(2)
            .sub(a * c * 4)
            == val;
    }
}
fn integerq(p: &str) -> impl Fn(&mut EGraph, Id, &Subst) -> bool {
    let p = p.parse().unwrap();
    move |egraph, _, subst| {
        let p = &egraph[subst[p]].data.clone().expect("here?").0;
        return p
            .sub(Num::new(1, 2))
            .is_zero();
    }
}
#[rustfmt::skip]
pub fn rules() -> Vec<Rewrite> {
    
     vec![
    rw!("comm-add";  "(+ ?a ?b)"        => "(+ ?b ?a)"),
    rw!("comm-mul";  "(* ?a ?b)"        => "(* ?b ?a)"),
    rw!("assoc-add"; "(+ ?a (+ ?b ?c))" => "(+ (+ ?a ?b) ?c)"),
    rw!("assoc-mul"; "(* ?a (* ?b ?c))" => "(* (* ?a ?b) ?c)"),

    rw!("sub-canon"; "(- ?a ?b)" => "(+ ?a (* -1 ?b))"),
    rw!("div-canon"; "(/ ?a ?b)" => "(* ?a (^ ?b -1))" if is_not_zero("?b")),
    // rw!("canon-sub"; "(+ ?a (* -1 ?b))"   => "(- ?a ?b)"),
    // rw!("canon-div"; "(* ?a (^ ?b -1))" => "(/ ?a ?b)" if is_not_zero("?b")),

    rw!("zero-add"; "(+ ?a 0)" => "?a"),
    rw!("zero-mul"; "(* ?a 0)" => "0"),
    rw!("one-mul";  "(* ?a 1)" => "?a"),

    rw!("add-zero"; "?a" => "(+ ?a 0)"),
    rw!("mul-one";  "?a" => "(* ?a 1)"),

    rw!("cancel-sub"; "(- ?a ?a)" => "0"),
    rw!("cancel-div"; "(/ ?a ?a)" => "1" if is_not_zero("?a")),

    rw!("distribute"; "(* ?a (+ ?b ?c))"        => "(+ (* ?a ?b) (* ?a ?c))"),
    rw!("factor"    ; "(+ (* ?a ?b) (* ?a ?c))" => "(* ?a (+ ?b ?c))"),

    rw!("pow-mul"; "(* (^ ?a ?b) (^ ?a ?c))" => "(^ ?a (+ ?b ?c))"),
    rw!("pow0"; "(^ ?x 0)" => "1"
        if is_not_zero("?x")),
    rw!("pow1"; "(^ ?x 1)" => "?x"),
    rw!("pow2"; "(^ ?x 2)" => "(* ?x ?x)"),
    rw!("pow-recip"; "(^ ?x -1)" => "(/ 1 ?x)"
        if is_not_zero("?x")),
    rw!("recip-mul-div"; "(* ?x (/ 1 ?x))" => "1" if is_not_zero("?x")),

    rw!("d-variable"; "(d ?x ?x)" => "1" if is_sym("?x")),
    rw!("d-constant"; "(d ?x ?c)" => "0" if is_sym("?x") if freeq("?c", "?x")),

    rw!("d-add"; "(d ?x (+ ?a ?b))" => "(+ (d ?x ?a) (d ?x ?b))"),
    rw!("d-mul"; "(d ?x (* ?a ?b))" => "(+ (* ?a (d ?x ?b)) (* ?b (d ?x ?a)))"),

    rw!("d-sin"; "(d ?x (sin ?x))" => "(cos ?x)"),
    rw!("d-cos"; "(d ?x (cos ?x))" => "(* -1 (sin ?x))"),

    rw!("d-ln"; "(d ?x (ln ?x))" => "(/ 1 ?x)" if is_not_zero("?x")),

    rw!("d-power";
        "(d ?x (^ ?f ?g))" =>
        "(* (^ ?f ?g)
            (+ (* (d ?x ?f)
                  (/ ?g ?f))
               (* (d ?x ?g)
                  (ln ?f))))"
        if is_not_zero("?f")
        if is_not_zero("?g")
    ),
    rw!("i-coff"; "(i (* ?c ?a) ?x)" => "(* ?c (i ?a ?x))" if freeq("?c", "?x")),
    rw!("i-one"; "(i 1 ?x)" => "?x"),
    rw!("i-cos"; "(i (cos ?x) ?x)" => "(sin ?x)"),
    rw!("i-sin"; "(i (sin ?x) ?x)" => "(* -1 (cos ?x))"),
    rw!("i-sum"; "(i (+ ?f ?g) ?x)" => "(+ (i ?f ?x) (i ?g ?x))"),
    rw!("i-dif"; "(i (- ?f ?g) ?x)" => "(- (i ?f ?x) (i ?g ?x))"),
    rw!("i-parts"; "(i (* ?a ?b) ?x)" =>
        "(- (* ?a (i ?b ?x)) (i (* (d ?x ?a) (i ?b ?x)) ?x))"),

    // ---------------------
    rw!("1.1.1.1.1"; "(i (/ 1 ?x) ?x)" => "(ln ?x)" ),
    // Int[x_^m_., x_Symbol] := x^(m + 1)/(m + 1) /; FreeQ[m, x] && NeQ[m, -1]
    rw!("1.1.1.1.2"; "(i (^ ?x ?m) ?x)" => "(/ (^ ?x (+ ?m 1)) (+ ?m 1))"),
    // Int[(a_. + b_.*x_)^m_, x_Symbol] := (a + b*x)^(m + 1)/(b*(m + 1)) /; FreeQ[{a, b, m}, x] && NeQ[m, -1]
    rw!("1.1.1.1.4"; r"(i (^ (+ ?a (* ?b ?x)) ?m) ?x)" => "(/ (^ (+ ?a (* ?b ?x)) (+ ?m 1)) (* ?b (+ ?m 1)))"
    if freeq("?a", "?x")
    if freeq("?b", "?x")
    if freeq("?m", "?x")
    if neq("?m", 1.into())
    ),
    rw!("1.2.2.1.6"; "(i (^ (+ ?a   (+ (* ?b   (^ ?x   2))   (* ?c   (^ ?x   4))))   ?p) ?x)" => "(* (^ (+ ?b   (* 2   (* ?c   (^ ?x   2))))   (* -2   ?p))   (* (^ (+ ?a   (+ (* ?b   (^ ?x   2))   (* ?c   (^ ?x   4))))   ?p)   (i (^ (+ ?b   (* 2   (* ?c   (^ ?x   2))))   (* 2   ?p))  ?x)))"  if freeq("?a", "?x") if freeq("?p", "?x") if freeq("?b", "?x") if freeq("?c", "?x")
    if b2_4ac("?b", "?a", "?c", 0.into()) 
    if integerq("?p")
    ),
    rw!("try tri"; "(i (* (^ (* ?b   (cos (+ ?e   (* ?f   ?x))))   ?n)   (^ (* ?a   (sin (+ ?e   (* ?f   ?x))))   ?m)) ?x)" => "(/ (/ (/ (/ (* (^ (* ?b   (cos (+ ?e   (* ?f   ?x))))   (+ 1   ?n))   (^ (* ?a   (sin (+ ?e   (* ?f   ?x))))   (+ 1   ?m)))   (+ 1   ?m))   ?f)   ?b)   ?a)")
    ]}

#[cfg(test)]
mod test {
    use std::ops::Not;

    use super::*;
    #[test]
    fn test_int() {
        let rules = rules();
        for start in ["(i (+ (* a (sin x)) (^ x m)) x)", "(i (/ 5 x) x)", 
        "(i (* (^ (* 9   (cos (+ eee   (* f   x))))   n)   (^ (* 6   (sin (+ eee   (* f   x))))   m)) x)"] {
            let start = start.parse().unwrap();
            let mut runner = Runner::default()
                .with_explanations_enabled()
                .with_expr(&start)
                .run(&rules);
            let extractor = Extractor::new(&runner.egraph, MathCostFn);
            let (_best_cost, best_expr) = extractor.find_best(runner.roots[0]);
            assert!(&best_expr.to_string().contains("(i").not());
            dbg!(runner
                .explain_equivalence(&start, &best_expr)
                .get_flat_strings());
        }
    }
}

fn main() {
    println!("hello world");
}
