import Symbolism

inductive Expr where
  | int : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  | pow : Expr → Expr → Expr
deriving Repr, DecidableEq

namespace Expr

instance : OfNat Expr n where
  ofNat := Expr.int n

instance : Add Expr where
  add := Expr.add

instance : Mul Expr where
  mul := Expr.mul

instance : Pow Expr Expr where
  pow := Expr.pow

instance : Pow Expr Nat where
  pow a n := Expr.pow a (Expr.int n)

def neg (e : Expr) : Expr := Expr.mul (Expr.int (-1)) e

def sub (a b : Expr) : Expr := Expr.add a (neg b)

def div (a b : Expr) : Expr := Expr.mul a (Expr.pow b (Expr.int (-1)))

def mk_add (a b : Expr) : Expr :=
  match a, b with
  | Expr.int 0, e => e
  | e, Expr.int 0 => e
  | Expr.int m, Expr.int n => Expr.int (m + n)
  | e1, e2 => Expr.add e1 e2

def mk_mul (a b : Expr) : Expr :=
  match a, b with
  | Expr.int 0, _ => Expr.int 0
  | _, Expr.int 0 => Expr.int 0
  | Expr.int 1, e => e
  | e, Expr.int 1 => e
  | Expr.int m, Expr.int n => Expr.int (m * n)
  | e1, e2 => Expr.mul e1 e2

def mk_pow (a b : Expr) : Expr :=
  match a, b with
  | _, .int 0 => Expr.int 1
  | e, .int 1 => e
  | .int m, .int n =>
    if n >= 0 then
      Expr.int (m ^ n.natAbs)
    else
      Expr.pow (Expr.int m) (Expr.int n)
  | e1, e2 => Expr.pow e1 e2

def simplify : Expr → Expr
  | Expr.int n => Expr.int n
  | Expr.var x => Expr.var x
  | Expr.add a b => mk_add (simplify a) (simplify b)
  | Expr.mul a b => mk_mul (simplify a) (simplify b)
  | Expr.pow a b => mk_pow (simplify a) (simplify b)

end Expr

-- ------------------------------------------------------------

def x : Expr := Expr.var "x"
def y : Expr := Expr.var "y"

#eval repr (x + 3 * y)
#eval repr (Expr.neg x)

#eval repr (Expr.simplify (x + 0))

#eval repr (Expr.simplify (x + x))

#eval repr (3 + 4 + x)

#eval repr (Expr.simplify (3 + 4 + x))

#eval repr (Expr.simplify (3 + x + 7))

#eval repr (Expr.simplify (x * 0))
#eval repr (Expr.simplify (x * 1))

#eval repr (Expr.simplify (x ^ Expr.int 0))
#eval repr (Expr.simplify (x ^ Expr.int 1))

#eval repr (Expr.simplify (x ^ 0))
#eval repr (Expr.simplify (x ^ 1))
