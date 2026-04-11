inductive Expr where
  | rat : Rat -> Expr
  | var : String -> Expr
  | add : Expr -> Expr -> Expr
  | mul : Expr -> Expr -> Expr
  | pow : Expr -> Expr -> Expr
deriving Repr, DecidableEq

namespace Expr

instance : OfNat Expr n where ofNat := .rat n

instance : Add Expr where add := .add

instance : Mul Expr where mul := .mul

instance : Pow Expr Expr where pow := .pow

instance : Pow Expr Nat where pow a n := .pow a (.rat n)

def neg (e : Expr) : Expr := .mul (.rat (-1)) e

def sub (a b : Expr) : Expr := .add a (neg b)

def div (a b : Expr) : Expr := .mul a (.pow b (.rat (-1)))

def mk_add (a b : Expr) : Expr :=
  match a, b with
  | .rat 0,      e => e
  |      e, .rat 0 => e
  | .rat m, .rat n => .rat (m + n)
  |      _,      _ => .add a b

def mk_mul (a b : Expr) : Expr :=
  match a, b with
  | .rat 0,      _ => .rat 0
  |      _, .rat 0 => .rat 0
  | .rat 1,      e => e
  |      e, .rat 1 => e
  | .rat m, .rat n => .rat (m * n)
  |      _,      _ => .mul a b

def mk_pow (a b : Expr) : Expr :=
  match a, b with
  |      _, .rat 0 => .rat 1
  |      e, .rat 1 =>      e
  | .rat m, .rat n =>
    if n.isInt then
      if n >= 0 then
        .rat (m ^ n.num.natAbs)
      else if m == 0 then
        .pow (.rat m) (.rat n)
      else
        .rat (1 / (m ^ n.num.natAbs))
    else
      .pow (.rat m) (.rat n)
  | _, _ => .pow a b


def simplify : Expr -> Expr
  | .rat n => .rat n
  | .var x => .var x
  | .add a b => mk_add (simplify a) (simplify b)
  | .mul a b => mk_mul (simplify a) (simplify b)
  | .pow a b => mk_pow (simplify a) (simplify b)

end Expr
