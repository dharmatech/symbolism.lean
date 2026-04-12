# symbolism.lean

This is a very basic computer algebra simplifier written in the [Lean programming language](https://lean-lang.org/).

It's roughly based on the simplifier in the [Symbolism computer algebra library for C#](https://github.com/dharmatech/Symbolism).\
That is in turn based on the [mpl computer algebra library for Scheme](https://github.com/dharmatech/mpl).\
Which is based on the algorithms found in the books *Computer Algebra and Symbolic Computation* by Joel S. Cohen.

For examples of the expressions it can simplify, see the file [SymbolismTests.lean](SymbolismTests.lean).

Some examples from the unit tests:

```
def x : Expr := Expr.var "x"
def y : Expr := Expr.var "y"

#guard Expr.simplify (x * 0) == 0

#guard Expr.simplify (x + x) == 2 * x

#guard Expr.simplify ((2 * x * y) + (3 * x * y)) == 5 * x * y
```

The [current simplifier](Symbolism\Basic.lean) is less than 215 lines long.