use std::{collections::{HashMap, HashSet, VecDeque}, fmt, mem, str::Split};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Literal {
    variable: char,
    inverted: bool,
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.inverted {
            write!(f, "~")?;
        }
        write!(f, "{}", self.variable)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Expression {
    Constant(bool),
    Literal(Literal),
    Not(Box<Expression>),
    Implies(Box<Expression>, Box<Expression>),
    Equivalent(Box<Expression>, Box<Expression>),
    And(Vec<Expression>),
    Or(Vec<Expression>),
}

impl fmt::Display for Expression {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &Expression::Constant(c) => write!(f, "{}", if c { 'T' } else { 'F' }),
            Expression::Literal(l) => write!(f, "{}", l),
            Expression::Not(a) => write!(f, "~({})", a),
            Expression::Implies(a, b) => write!(f, "({}) ==> ({})", a, b),
            Expression::Equivalent(a, b) => write!(f, "({}) <==> ({})", a, b),
            Expression::And(xs) => {
                write!(f, "({})", xs[0])?;
                for x in xs.iter().skip(1) {
                    write!(f, " & ({})", x)?;
                }
                Ok(())
            }
            Expression::Or(xs) => {
                write!(f, "({}) ", xs[0])?;
                for x in xs.iter().skip(1) {
                    write!(f, " | ({})", x)?;
                }
                Ok(())
            }
        }
    }
}

impl Expression {
    fn parse_inner(tokens: &mut Split<char>) -> Expression {
        let mut stack = VecDeque::new();
        while let Some(token) = tokens.next() {
            dbg!(&token, &stack);
            match token {
                "!" => {
                    let e = stack.pop_back().unwrap();
                    stack.push_back(Expression::Not(Box::new(e)));
                }
                "T" => stack.push_back(Expression::Constant(true)),
                "F" => stack.push_back(Expression::Constant(false)),
                "==>" => {
                    let right = stack.pop_back().unwrap();
                    let left = stack.pop_back().unwrap();
                    stack.push_back(Expression::Implies(
                        Box::new(left),
                        Box::new(right)));
                    },
                "<==>" => {
                    let right = stack.pop_back().unwrap();
                    let left = stack.pop_back().unwrap();
                    stack.push_back(Expression::Equivalent(
                        Box::new(left),
                        Box::new(right)));
                    },
                "&" => {
                    let right = stack.pop_back().unwrap();
                    let left = stack.pop_back().unwrap();
                    stack.push_back(Expression::And(vec![
                        left,
                        right
                    ]));
                }
                "|" => {
                    let right = stack.pop_back().unwrap();
                    let left = stack.pop_back().unwrap();
                    stack.push_back(Expression::Or(vec![
                        left,
                        right
                    ]));
                },
                s if s.len() == 1 && s.chars().next().unwrap().is_ascii_alphabetic() => {
                    stack.push_back(Expression::Literal(Literal {
                        variable: s.chars().next().unwrap(),
                        inverted: false
                    }));
                },
                s => panic!("what is '{}'", s),
            }
        }
        assert_eq!(stack.len(), 1);
        stack.pop_back().unwrap()
    }

    fn parse(s: &str) -> Expression {
        let mut tokens = s.split(' ');
        Expression::parse_inner(&mut tokens)
    }

    fn eval(&self, values: &HashMap<char, bool>) -> bool {
        match self {
            Expression::Constant(c) => *c,
            Expression::Literal(l) => values[&l.variable] ^ l.inverted,
            Expression::Not(a) => !a.eval(values),
            Expression::Implies(a, b) => !a.eval(values) || b.eval(values),
            Expression::Equivalent(a, b) => a.eval(values) == b.eval(values),
            Expression::And(xs) => xs.iter().all(|x| x.eval(values)),
            Expression::Or(xs) => xs.iter().any(|x| x.eval(values)),
        }
    }

    fn recurse<B: FnMut(&Expression)>(&self, before: &mut B) {
        before(self);
        match self {
            Expression::Literal(_) | Expression::Constant(_) => {}
            Expression::Not(inner) => {
                inner.recurse(before);
            }
            Expression::Equivalent(a, b) | Expression::Implies(a, b) => {
                a.recurse(before);
                b.recurse(before);
            }
            Expression::And(xs) | Expression::Or(xs) => {
                for x in xs {
                    x.recurse(before);
                }
            }
        }
    }

    fn recurse_mut<B: FnMut(&mut Expression)>(&mut self, before: &mut B) {
        before(self);
        match self {
            Expression::Literal(_) | Expression::Constant(_) => {}
            Expression::Not(inner) => {
                inner.recurse_mut(before);
            }
            Expression::Equivalent(a, b) | Expression::Implies(a, b) => {
                a.recurse_mut(before);
                b.recurse_mut(before);
            }
            Expression::And(xs) | Expression::Or(xs) => {
                for x in xs {
                    x.recurse_mut(before);
                }
            }
        }
    }

    fn sort(&mut self) -> bool {
        fn is_sorted<T: Ord>(data: &[T]) -> bool {
            data.windows(2).all(|w| w[0] <= w[1])
        }

        let mut modified = false;
        self.recurse_mut(&mut |e| match e {
            Expression::And(ref mut xs) | Expression::Or(ref mut xs) => {
                if !is_sorted(xs) {
                    xs.sort();
                    modified = true;
                }
            }
            Expression::Equivalent(ref mut a, ref mut b) => {
                if *a > *b {
                    mem::swap(a, b);
                    modified = true;
                }
            }
            _ => {}
        });
        modified
    }

    fn simplify_implies(&mut self) -> bool {
        let mut modified = false;
        self.recurse_mut(&mut |e| {
            take_mut::take(e, |e| match e {
                Expression::Implies(a, b) => {
                    modified = true;
                    // dbg!(&a, &b);
                    Expression::Or(vec![Expression::Not(a), *b])
                }
                e => e,
            });
        });
        modified
    }

    fn simplify_equivalence(&mut self) -> bool {
        let mut modified = false;
        self.recurse_mut(&mut |e| {
            take_mut::take(e, |e| match e {
                Expression::Equivalent(a, b) => {
                    modified = true;
                    Expression::Or(vec![
                        Expression::And(vec![
                            Expression::Not(a.clone()),
                            Expression::Not(b.clone()),
                        ]),
                        Expression::And(vec![*a, *b]),
                    ])
                }
                e => e,
            });
        });
        modified
    }

    fn simplify_not(&mut self) -> bool {
        let mut modified = false;

        self.recurse_mut(&mut |orig| {
            // let before = orig.clone();
            take_mut::take(orig, |e| match e {
                Expression::Not(inverted) => match *inverted {
                    Expression::Or(xs) => {
                        modified = true;
                        Expression::And(
                            xs.into_iter()
                                .map(|x| Expression::Not(Box::new(x)))
                                .collect(),
                        )
                    }
                    Expression::And(xs) => {
                        modified = true;
                        Expression::Or(
                            xs.into_iter()
                                .map(|x| Expression::Not(Box::new(x)))
                                .collect(),
                        )
                    }
                    Expression::Literal(l) => {
                        modified = true;
                        Expression::Literal(Literal {
                            variable: l.variable,
                            inverted: !l.inverted,
                        })
                    }
                    e => Expression::Not(Box::new(e)),
                },
                e => e,
            });
            // before.assert_equivalent(&orig);
        });
        modified
    }

    fn flatten(&mut self) -> bool {
        let mut modified = false;
        self.recurse_mut(&mut |e| {
            take_mut::take(e, |e| match e {
                // A v B v (C v D)
                // into
                // A v B v C v D
                Expression::Or(mut xs) => {
                    let first_or = xs
                        .iter()
                        .enumerate()
                        .filter(|x| {
                            if let (_, Expression::Or(_)) = x {
                                true
                            } else {
                                false
                            }
                        })
                        .map(|x| x.0)
                        .next();
                    if let Some(or_index) = first_or {
                        let or = xs.remove(or_index);
                        if let Expression::Or(inner_xs) = or {
                            modified = true;
                            for inner_x in inner_xs {
                                xs.push(inner_x);
                            }
                            Expression::Or(xs)
                        } else {
                            panic!();
                        }
                    } else {
                        Expression::Or(xs)
                    }
                }
                // A ^ B ^ (C ^ D)
                // into
                // A ^ B ^ C ^ D
                Expression::And(mut xs) => {
                    let first_and = xs
                        .iter()
                        .enumerate()
                        .filter(|x| {
                            if let (_, Expression::And(_)) = x {
                                true
                            } else {
                                false
                            }
                        })
                        .map(|x| x.0)
                        .next();
                    if let Some(and_index) = first_and {
                        let and = xs.remove(and_index);
                        if let Expression::And(inner_xs) = and {
                            modified = true;
                            for inner_x in inner_xs {
                                xs.push(inner_x);
                            }
                            Expression::And(xs)
                        } else {
                            panic!();
                        }
                    } else {
                        Expression::And(xs)
                    }
                }
                e => e,
            })
        });
        modified
    }

    fn simplify_distribute(&mut self) -> bool {
        let mut modified = false;
        self.recurse_mut(&mut |e| {
            take_mut::take(e, |e| match e {
                // A v B v (C ^ D)
                // into
                // (A v B v C) ^ (A v B v D)
                Expression::Or(mut xs) => {
                    let first_and = xs
                        .iter()
                        .enumerate()
                        .filter(|x| {
                            if let (_, Expression::And(_)) = x {
                                true
                            } else {
                                false
                            }
                        })
                        .map(|x| x.0)
                        .next();
                    if let Some(and_index) = first_and {
                        let and = xs.remove(and_index);
                        if let Expression::And(and_xs) = and {
                            modified = true;
                            Expression::And(
                                and_xs
                                    .into_iter()
                                    .map(|and_x| {
                                        let mut ors: Vec<Expression> = xs.iter().cloned().collect();
                                        ors.push(and_x);
                                        Expression::Or(ors)
                                    })
                                    .collect(),
                            )
                        } else {
                            panic!();
                        }
                    } else {
                        Expression::Or(xs)
                    }
                }
                e => e,
            })
        });
        modified
    }

    fn simplify(&mut self) {
        let before = self.clone();
        println!("Before             simplify: {}", &self);
        loop {
            if self.simplify_implies() {
                println!(" After     simplify_implies: {}", &self);
                self.assert_equivalent(&before);
                continue;
            }
            if self.simplify_equivalence() {
                println!(" After simplify_equivalence: {}", &self);
                self.assert_equivalent(&before);
                continue;
            }
            if self.simplify_not() {
                println!(" After         simplify_not: {}", &self);
                self.assert_equivalent(&before);
                continue;
            }
            if self.simplify_distribute() {
                println!(" After  simplify_distribute: {}", &self);
                self.assert_equivalent(&before);
                continue;
            }
            if self.flatten() {
                println!(" After              flatten: {}", &self);
                self.assert_equivalent(&before);
                continue;
            }
            if self.sort() {
                println!(" After                 sort: {}", &self);
                self.assert_equivalent(&before);
                continue;
            }
            break;
        }
    }

    fn to_clause(&self) -> Clause {
        if let Expression::Or(literals) = self {
            Clause(
                literals
                    .iter()
                    .map(|l| {
                        if let Expression::Literal(l) = l {
                            l.clone()
                        } else {
                            panic!("Expected literal!");
                        }
                    })
                    .collect(),
            )
        } else {
            panic!("Expected Or!");
        }
    }

    fn to_cnf(&self) -> Cnf {
        match self {
            Expression::Or(_) => {
                Cnf(vec![self.to_clause()])
            }
            Expression::And(clauses) => {
                Cnf(clauses
                    .iter()
                    .map(|c| c.to_clause())
                    .collect())
            }
            _ => panic!("Expected And!"),
        }
    }

    fn find_vars(&self) -> HashSet<char> {
        let mut chars = HashSet::new();

        self.recurse(&mut |e| {
            if let Expression::Literal(l) = e {
                chars.insert(l.variable);
            }
        });

        chars
    }

    fn assert_equivalent_helper(
        &self,
        other: &Expression,
        vars_to_set: &mut HashSet<char>,
        values: &mut HashMap<char, bool>,
    ) {
        if vars_to_set.len() == 0 {
            let self_result = self.eval(values);
            let other_result = other.eval(values);
            if self_result != other_result {
                panic!(
                    "For {:?},\n{} resolved to {}, but\n{} resolved to {}.",
                    &values, &self, self_result, &other, other_result
                );
            }
        } else {
            let v = *vars_to_set.iter().next().unwrap();
            vars_to_set.remove(&v);
            values.insert(v, false);
            self.assert_equivalent_helper(other, vars_to_set, values);
            values.remove(&v);
            values.insert(v, true);
            self.assert_equivalent_helper(other, vars_to_set, values);
            values.remove(&v);
            vars_to_set.insert(v);
        }
    }

    fn assert_equivalent(&self, other: &Expression) {
        let mut my_vars = self.find_vars();
        let other_vars = other.find_vars();
        assert_eq!(&my_vars, &other_vars);

        let mut values = HashMap::new();
        self.assert_equivalent_helper(other, &mut my_vars, &mut values);
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Clause(HashSet<Literal>);
impl Clause {
    fn simplify(&mut self) {
        let positives: HashSet<_>= self.0.iter()
            .filter(|l| !l.inverted)
            .map(|l| l.variable)
            .collect();
        let negatives = self.0.iter()
            .filter(|l| l.inverted)
            .map(|l| l.variable)
            .collect();
        if None != positives.intersection(&negatives).next() {
            self.0.clear();
        }
    }
    

    fn eval(&self, values: &HashMap<char, bool>) -> bool {
        self.0.iter().any(|l| l.inverted ^ values[&l.variable])
    }
}

impl fmt::Display for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(l) = self.0.iter().next() {
            write!(f, "{}", l)?;
            for c in self.0.iter().skip(1) {
                write!(f, " v {}", c)?;
            }
            Ok(())
        } else {
            write!(f,"{{}}")
        }
    }
}

#[derive(Debug)]
struct Cnf(Vec<Clause>);
impl Cnf {
    fn solve(&mut self) {
        for c in &mut self.0 {
            c.simplify();
        }

        self.0 = self.0.iter().filter(|c| c.0.len() > 0).cloned().collect();
    }
}

impl fmt::Display for Cnf {
    // This trait requires `fmt` with this exact signature.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if let Some(l) = self.0.iter().next() {
            write!(f, "({})", l)?;
            for c in self.0.iter().skip(1) {
                write!(f, " ^ ({})", c)?;
            }
            Ok(())
        } else {
            write!(f,"{{}}")
        }
    }
}

fn main() {
    let mut expression = Expression::parse(
        "B A & A ==>"
    );

    println!("{}", &expression);
    expression.simplify();
    println!(" simplified: {}", &expression);
    let mut cnf = expression.to_cnf();
    println!("as cnf: {}", &cnf);
    cnf.solve();
    println!("{}", &cnf);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test(before: Expression, after: Expression, expected: Expression) {
        println!(" Before: {}", &before);
        println!("   After: {}", &after);
        before.assert_equivalent(&after);
        println!("Expected: {}", &expected);
        before.assert_equivalent(&expected);
        assert_eq!(after, expected);
    }

    #[test]
    fn sort() {
        let before = Expression::parse("A B |");
        let mut after = before.clone();
        after.sort();
        let mut expected = Expression::parse("B A |");
        expected.sort();
        test(before, after, expected);
    }

    #[test]
    fn implies() {
        let before = Expression::parse("A B ==>");
        let mut after = before.clone();
        after.simplify_implies();
        let expected = Expression::parse("A ! B |");
        test(before, after, expected);
    }

    #[test]
    fn equivalence() {
        let before = Expression::parse("A B <==>");
        let mut after = before.clone();
        after.simplify_equivalence();
        let expected = Expression::parse("A ! B ! & A B & |");
        test(before, after, expected);
    }
}
