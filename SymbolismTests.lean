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

#guard Expr.simplify (x ^ Expr.int 0) == 1
#guard Expr.simplify (x ^ Expr.int 1) == x

#guard Expr.simplify (x ^ 0) == 1
#guard Expr.simplify (x ^ 1) == x

end SymbolismTests
