inductive Expr where
  | int : Int -> Expr
  | var : String -> Expr
  | add : Expr -> Expr -> Expr
  | mul : Expr -> Expr -> Expr
  | pow : Expr -> Expr -> Expr
deriving Repr, DecidableEq

namespace Expr

instance : OfNat Expr n where ofNat := .int n

instance : Add Expr where add := .add

instance : Mul Expr where mul := .mul

instance : Pow Expr Expr where pow := .pow

instance : Pow Expr Nat where pow a n := .pow a (.int n)

def neg (e : Expr) : Expr := .mul (.int (-1)) e

def sub (a b : Expr) : Expr := .add a (neg b)

def div (a b : Expr) : Expr := .mul a (.pow b (.int (-1)))

def mk_add (a b : Expr) : Expr :=
  match a, b with
  | .int 0,      e => e
  |      e, .int 0 => e
  | .int m, .int n => .int (m + n)
  |      _,      _ => .add a b

def mk_mul (a b : Expr) : Expr :=
  match a, b with
  | .int 0,      _ => .int 0
  |      _, .int 0 => .int 0
  | .int 1,      e => e
  |      e, .int 1 => e
  | .int m, .int n => .int (m * n)
  |      _,      _ => .mul a b

def mk_pow (a b : Expr) : Expr :=
  match a, b with
  |      _, .int 0 => .int 1
  |      e, .int 1 =>      e
  | .int m, .int n =>
    if n >= 0 then
      .int (m ^ n.natAbs)
    else
      .pow (.int m) (.int n)
  | _, _ => .pow a b

def simplify : Expr -> Expr
  | .int n => .int n
  | .var x => .var x
  | .add a b => mk_add (simplify a) (simplify b)
  | .mul a b => mk_mul (simplify a) (simplify b)
  | .pow a b => mk_pow (simplify a) (simplify b)

end Expr
