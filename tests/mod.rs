use color_eyre::Result;
use im_rc::HashSet;
use pax::{checkable::Checkable, Context, Environment, Identifier, Type};

#[test]
fn check() -> Result<()> {
    let mut env = Environment::new();
    let mut ctx = Context::new();

    ctx.insert(
        "Void".to_owned(),
        "U(0)".parse::<Checkable>()?.evaluate(&env),
    );

    ctx.insert(
        "Not".to_owned(),
        "U(0) →  U(0)".parse::<Checkable>()?.evaluate(&env),
    );

    env.insert(
        "Not".to_owned(),
        "λ A. A →  Void".parse::<Checkable>()?.evaluate(&env),
    );

    let samples = [
        (
            "λ _A. λ _B. λ a. λ _b. a",
            "Π (A : U(0)). Π (B : U(0)). A →  B →  A",
            1,
        ),
        ("U(1) →  U(2)", "U(3)", 4),
        ("U(0)", "U(10)", 11),
        (
            "λ _P. λ _Q. λ pq. λ nq. λ p. nq(pq(p))",
            "Π (P : U(0)). Π (Q : U(0)). (P →  Q) →  Not(Q) →  Not(P)",
            1,
        ),
    ];

    for (a, t, i) in samples {
        let t: Checkable = t.parse()?;
        let a: Checkable = a.parse()?;

        t.check(i, &Type::Universe(i), &ctx, &env)?;
        a.check(i, &t.evaluate(&env), &ctx, &env)?;
    }

    Ok(())
}

#[test]
fn alpha_eq() -> Result<()> {
    let samples = [("λ x. f(x)", "λ y. f(y)")];

    for (a, b) in samples {
        let a: Checkable = a.parse()?;
        let b: Checkable = b.parse()?;

        assert!(a.alpha_eq(&b));
    }

    Ok(())
}

#[test]
fn convert() -> Result<()> {
    let mut env = Environment::new();
    let ctx = HashSet::<Identifier>::new();

    let id: Checkable = "λ x. x".parse()?;
    env.insert("id".to_owned(), id.evaluate(&env));

    let samples = [
        ("λ x. id(x)", "λ y. y"),
        ("λ x. f(x)", "f"),
        ("(A →  B) →  (C →  D)", "(A →  B) →  C →  D"),
    ];

    for (a, b) in samples {
        let a: Checkable = a.parse()?;
        let b: Checkable = b.parse()?;

        assert!(a.convert(&b, &ctx, &env));
    }

    Ok(())
}

#[test]
fn natural_induction() -> Result<()> {
    let mut env = Environment::new();
    let mut ctx = Context::new();
    let i = 0;

    let add: Checkable =
        "λ m. indNat(_m. Nat →  Nat, λ n. n, _m. g. λ n. succ(g(n)), m)".parse()?;

    let t = Type::Function(
        Type::Natural.into(),
        Type::Function(Type::Natural.into(), Type::Natural.into()).into(),
    );

    add.check(i, &t, &ctx, &env)?;
    ctx.insert("add".to_owned(), t);
    env.insert("add".to_owned(), add.evaluate(&env));

    let sum: Checkable = "add(3, 4)".parse()?;
    sum.check(i, &Type::Natural, &ctx, &env)?;

    assert!(sum.evaluate(&env).convert(
        &"7".parse::<Checkable>()?.evaluate(&env),
        &ctx.iter().map(|(x, _)| x).collect()
    ));

    Ok(())
}
