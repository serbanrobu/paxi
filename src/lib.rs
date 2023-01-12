mod checkable;
mod inferable;
mod parser;
mod value;

use im_rc::HashMap;
use value::Value;

type Level = u8;

type Lift = u8;

type Identifier = String;

type Type = Value;

type Context = HashMap<Identifier, (Type, Option<Value>)>;

type Environment = HashMap<Identifier, Value>;

#[cfg(test)]
mod tests {
    use crate::checkable::Checkable;

    use super::*;

    #[test]
    fn check() {
        let mut env = HashMap::new();
        let mut ctx = HashMap::new();

        ctx.insert(
            "Void".to_owned(),
            (
                "U(0)"
                    .parse::<Checkable>()
                    .expect("should parse checkable")
                    .evaluate(&env),
                None,
            ),
        );

        ctx.insert(
            "Not".to_owned(),
            (
                "U(0) →  U(0)"
                    .parse::<Checkable>()
                    .expect("should parse checkable")
                    .evaluate(&env),
                None,
            ),
        );

        env.insert(
            "Not".to_owned(),
            "λ A. A →  Void"
                .parse::<Checkable>()
                .expect("should parse checkable")
                .evaluate(&env),
        );

        let samples = [
            ("λ _A. λ a. a", "Π (A : U(0)). ↑(A →  A)", 1),
            (
                "λ _A. λ _B. λ a. λ _b. a",
                "Π (A : U(0)). Π (B : U(0)). ↑(A →  B →  A)",
                1,
            ),
            ("U(1) →  U(2)", "U(3)", 4),
            ("U(0)", "U(100)", 101),
            (
                "λ _P. λ _Q. λ pq. λ nq. λ p. nq(pq(p))",
                "Π (P : U(0)). Π (Q : U(0)). ↑((P →  Q) →  Not(Q) →  Not(P))",
                1,
            ),
        ];

        for (a, t, i) in samples {
            let t: Checkable = t.parse().expect("should parse checkable");
            let a: Checkable = a.parse().expect("should parse checkable");

            t.check(&Type::Universe(i), &ctx)
                .expect("should parse checkable");
            a.check(&t.evaluate(&env), &ctx)
                .expect("should parse checkable");
        }
    }

    #[test]
    fn alpha_eq() {
        let samples = [("λ x. f(x)", "λ y. f(y)")];

        for (a, b) in samples {
            let a: Checkable = a.parse().expect("should parse checkable");
            let b: Checkable = b.parse().expect("should parse checkable");

            assert!(a.alpha_eq(&b));
        }
    }

    #[test]
    fn convert() {
        let mut env = HashMap::new();

        let id: Checkable = "λ x. x".parse().expect("should parse checkable");
        env.insert("id".to_owned(), id.evaluate(&env));

        let samples = [
            ("λ x. id(x)", "λ y. y"),
            ("λ x. f(x)", "f"),
            ("↑A(B)", "(↑A)(↑B)"),
            ("(A →  B) →  (C →  D)", "(A →  B) →  C →  D"),
        ];

        for (a, b) in samples {
            let a: Checkable = a.parse().expect("should parse checkable");
            let b: Checkable = b.parse().expect("should parse checkable");

            assert!(a.convert(&b, &env));
        }
    }
}
