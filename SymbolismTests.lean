import Symbolism

namespace SymbolismTests

def x : Expr := Expr.var "x"
def y : Expr := Expr.var "y"

-- #guard (x + 3 * y) == Expr.add x (Expr.mul 3 y)
-- #guard Expr.neg x == Expr.mul (Expr.int (-1)) x

#guard Expr.simplify (x + 0) == x
#guard Expr.simplify (x + x) == Expr.add x x

-- #guard (3 + 4 + x : Expr) == Expr.add (Expr.add 3 4) x
-- #guard Expr.simplify (3 + 4 + x) == Expr.add 7 x
-- #guard Expr.simplify (3 + x + 7) == Expr.add (Expr.add 3 x) 7

#guard Expr.simplify (x * 0) == 0
#guard Expr.simplify (x * 1) == x

#guard Expr.simplify (x ^ Expr.rat 0) == 1
#guard Expr.simplify (x ^ Expr.rat 1) == x

#guard Expr.simplify (x ^ 0) == 1
#guard Expr.simplify (x ^ 1) == x


-- #eval Expr.simplify (3 + x + 7)

#guard Expr.simplify (3 + x + 7) == 10 + x

-- #eval Expr.simplify (3 * x * 7)

#guard Expr.simplify (3 * x * 7) == 21 * x

-- #eval Expr.simplify ((3 + x) + (7 + y))

#guard Expr.simplify ((3 + x) + (7 + y)) == 10 + x + y

-- #eval Expr.simplify (x + (3 + y) + 7)

#guard Expr.simplify (x + (3 + y) + 7) == 10 + x + y

-- #eval Expr.simplify (x * (3 * y) * 7)

#guard Expr.simplify (x * (3 * y) * 7) == 21 * x * y



#eval Expr.simplify (0 + x + 0)

#guard Expr.simplify (0 + x + 0) == x

#guard Expr.simplify (1 * x * 1) == x

-- #eval Expr.simplify (0 * x * 7)

#guard Expr.simplify (0 * x * 7) == 0

-- #eval Expr.simplify (2 ^ (-3 : Expr))

-- #eval Expr.simplify (x + x)

#guard Expr.simplify (x + x) == 2 * x

-- #eval Expr.simplify (x + 3 * x)

#guard Expr.simplify (x + 3 * x) == 4 * x

#guard Expr.simplify (3 * x + 7 * x) == 10 * x

#guard Expr.simplify ((2 * x * y) + (3 * x * y)) == 5 * x * y

#guard Expr.simplify (x * x) == x ^ 2

#guard Expr.simplify ((x ^ 2) * (x ^ 3)) == x ^ 5

#guard Expr.simplify (2 * x * 3 * x) == 6 * x ^ 2

#guard Expr.simplify ((x ^ 2) * (x ^ Expr.rat (-2))) == 1

end SymbolismTests
