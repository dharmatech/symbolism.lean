import Symbolism

namespace SymbolismTests

def x : Expr := Expr.var "x"
def y : Expr := Expr.var "y"

#guard Expr.simplify (x + 0) == x

#guard Expr.simplify (x + x) == 2 * x

#guard Expr.simplify (x * 0) == 0

#guard Expr.simplify (x * 1) == x

#guard Expr.simplify (x ^ Expr.rat 0) == 1

#guard Expr.simplify (x ^ Expr.rat 1) == x

#guard Expr.simplify (x ^ 0) == 1

#guard Expr.simplify (x ^ 1) == x

#guard Expr.simplify (3 + x + 7) == 10 + x

#guard Expr.simplify (3 * x * 7) == 21 * x

#guard Expr.simplify ((3 + x) + (7 + y)) == 10 + x + y

#guard Expr.simplify (x * (3 * y) * 7) == 21 * x * y

#guard Expr.simplify (0 + x + 0) == x

#guard Expr.simplify (1 * x * 1) == x

#guard Expr.simplify (0 * x * 7) == 0

#guard Expr.simplify (x + x) == 2 * x

#guard Expr.simplify (x + 3 * x) == 4 * x

#guard Expr.simplify (3 * x + 7 * x) == 10 * x

#guard Expr.simplify ((2 * x * y) + (3 * x * y)) == 5 * x * y

#guard Expr.simplify (x * x) == x ^ 2

#guard Expr.simplify ((x ^ 2) * (x ^ 3)) == x ^ 5

#guard Expr.simplify (2 * x * 3 * x) == 6 * x ^ 2

#guard Expr.simplify ((x ^ 2) * (x ^ Expr.rat (-2))) == 1

#guard Expr.simplify (y + x) == x + y

#guard Expr.simplify (y * x) == x * y

#guard Expr.simplify (x + (3 + y) + 7) == 10 + x + y

#guard Expr.simplify (2 * x * y + 3 * y * x) == 5 * x * y

#guard Expr.simplify (2 * y * x + 3 * x * y) == 5 * x * y

#guard Expr.simplify (-x) == Expr.mul (Expr.rat (-1)) x

#guard Expr.simplify (x - y) == x + Expr.mul (Expr.rat (-1)) y

#guard Expr.simplify (x - x) == 0

#guard Expr.simplify ((x - y) + y) == x

#guard Expr.simplify (x / y) == x * (y ^ Expr.rat (-1))

#guard Expr.simplify (x / x) == 1

#guard Expr.simplify (x * (x ^ Expr.rat (-1))) == 1

end SymbolismTests
