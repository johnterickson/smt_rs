use std::{collections::HashMap, fmt, mem};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Literal {
    variable: char,
    inverted: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Expression {
    Literal(Literal),
    Not(Box<Expression>),
    Implies(Box<Expression>, Box<Expression>),
    Equivalent(Box<Expression>, Box<Expression>),
    And(Box<Expression>, Box<Expression>),
    Or(Box<Expression>, Box<Expression>),
}

impl fmt::Display for Expression {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Expression::Literal(l) => {
                if l.inverted {
                    write!(f, "~")?;
                }
                write!(f, "{}", l.variable)
            },
            Expression::Not(a) => write!(f, "~({})", a),
            Expression::Implies(a, b) => write!(f, "({}) ==> ({})", a, b),
            Expression::Equivalent(a, b) => write!(f, "({}) <==> ({})", a, b),
            Expression::And(a, b) => write!(f, "({}) & ({})", a, b),
            Expression::Or(a, b) => write!(f, "({}) | ({})", a, b),
        }
    }
}

impl Expression {
    fn eval(&self, values: &HashMap<char, bool>) -> bool {
        match self {
            Expression::Literal(l) => values[&l.variable] ^ l.inverted,
            Expression::Not(a) => !a.eval(values),
            Expression::Implies(a, b) => !a.eval(values) || b.eval(values),
            Expression::Equivalent(a, b) => a.eval(values) == b.eval(values),
            Expression::And(a, b) => a.eval(values) && b.eval(values),
            Expression::Or(a, b) => a.eval(values) || b.eval(values),
        }
    }

    fn recurse<B: Fn(&mut Expression)>(&mut self, before: &B) {
        before(self);
        match self {
            Expression::Literal(_) => {}
            Expression::Not(inner) => {
                inner.recurse(before);
            }
            Expression::Equivalent(a, b)
            | Expression::Implies(a, b)
            | Expression::And(a, b)
            | Expression::Or(a, b) => {
                a.recurse(before);
                b.recurse(before);
            }
        }
    }

    fn normalize(&mut self) {
        self.recurse(&|e| {
            match e {
                Expression::And(ref mut a, ref mut b) |
                Expression::Equivalent(ref mut a, ref mut b) |
                Expression::Or(ref mut a, ref mut b) => {
                    if *a > *b {
                        mem::swap(a.as_mut(), b.as_mut());
                    }
                }
                _ => {}
            }
        });
    }

    fn simplify_implies(&mut self) {
        self.recurse(&|e| {
            take_mut::take(e, |e| match e {
                Expression::Implies(a, b) => Expression::Or(Box::new(Expression::Not(a)), b),
                e => e,
            });
        });
    }

    fn simplify_equivalence(&mut self) {
        self.recurse(&|e| {
            take_mut::take(e, |e| match e {
                Expression::Equivalent(a, b) => Expression::Or(
                    Box::new(Expression::And(
                        Box::new(Expression::Not(a.clone())),
                        Box::new(Expression::Not(b.clone())),
                    )),
                    Box::new(Expression::And(a, b)),
                ),
                e => e,
            });
        });
    }

    fn simplify_not(&mut self) {
        self.recurse(
            &|e| {
                take_mut::take(e, |e| match e {
                    Expression::Not(inverted) => match *inverted {
                        Expression::Or(a, b) => Expression::And(
                            Box::new(Expression::Not(a)),
                            Box::new(Expression::Not(b)),
                        ),
                        Expression::And(a, b) => Expression::Or(
                            Box::new(Expression::Not(a)),
                            Box::new(Expression::Not(b)),
                        ),
                        Expression::Literal(l) => {
                            Expression::Literal(Literal {
                                variable: l.variable,
                                inverted: !l.inverted
                            })
                        }
                        e => e,
                    },
                    e => e,
                });
            }
        );
    }

    fn simplify_distribute(&mut self) {
        self.recurse(
            &|e| {
                take_mut::take(e, |e| match e {
                    Expression::Or(ref a, ref b) => match (a.as_ref(), b.as_ref()) {
                        (Expression::Literal(l), Expression::And(b, c)) |
                        (Expression::And(b, c), Expression::Literal(l)) => {
                            Expression::And(
                                Box::new(Expression::Or(Box::new(Expression::Literal(l.clone())), b.clone())),
                                Box::new(Expression::Or(Box::new(Expression::Literal(l.clone())), c.clone()))
                            )
                        },
                        (_, _) => e,
                    },
                    e => e,
                });
            }
        );
    }

    fn simplify(&mut self) {
        self.simplify_implies();
        self.simplify_equivalence();
        self.simplify_not();
        self.simplify_distribute();
    }
}

#[derive(Debug)]
struct Clause(Vec<Literal>);

#[derive(Debug)]
struct Cnf(Vec<Clause>);

fn main() {
    let mut expression = Expression::Not(Box::new(Expression::And(
        Box::new(Expression::Implies(
            Box::new(Expression::Literal(Literal {
                variable: 'a',
                inverted: false,
            })),
            Box::new(Expression::Literal(Literal {
                variable: 'b',
                inverted: false,
            })),
        )),
        Box::new(Expression::Equivalent(
            Box::new(Expression::Literal(Literal {
                variable: 'c',
                inverted: false,
            })),
            Box::new(Expression::Literal(Literal {
                variable: 'd',
                inverted: false,
            })),
        )),
    )));

    println!("{}", &expression);

    expression.simplify();
    expression.simplify();

    println!("{}", &expression);
    dbg!(&expression);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_var(v: char) -> Box<Expression> {
        Box::new(Expression::Literal(Literal {
            variable: v,
            inverted: false,
        }))
    }

    fn test(before: Expression, mut after: Expression, mut expected: Expression) {
        let mut values = HashMap::new();
        for a_val in [false, true] {
            values.clear();
            values.insert('a', a_val);
            for b_val in [false, true] {
                values.insert('b', b_val);
                assert_eq!(before.eval(&values), after.eval(&values));
            }
        }

        after.simplify();
        after.normalize();

        expected.simplify();
        expected.normalize();

        assert_eq!(after, expected);
    }

    #[test]
    fn implies() {
        let before = Expression::Implies(make_var('a'), make_var('b'));
        let mut after = before.clone();
        after.simplify_implies();
        let expected = Expression::Or(Box::new(Expression::Not(make_var('a'))), make_var('b'));

        test(before, after, expected);
    }

    #[test]
    fn equivalence() {
        let before = Expression::Equivalent(make_var('a'), make_var('b'));
        let mut after = before.clone();
        after.simplify_equivalence();
        let expected = Expression::Or(
            Box::new(Expression::And(
                Box::new(Expression::Not(make_var('a'))),
                Box::new(Expression::Not(make_var('b'))))),
            Box::new(Expression::And(
                    make_var('a'), 
                    make_var('b'))),
            );

        test(before, after, expected);
    }
}
