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

def add_terms : Expr → List Expr
  | .add a b => add_terms a ++ add_terms b
  | e => [e]

def mul_factors : Expr → List Expr
  | .mul a b => mul_factors a ++ mul_factors b
  | e => [e]

def from_add_terms : List Expr → Expr
  | [] => .rat 0
  | t :: ts => ts.foldl (fun acc e => .add acc e) t

def from_mul_factors : List Expr → Expr
  | [] => .rat 1
  | f :: fs => fs.foldl (fun acc e => .mul acc e) f

def normalize_add_terms (terms : List Expr) : List Expr :=
  let const := terms.foldl (fun acc e =>
    match e with
    | .rat q => acc + q
    | _ => acc) 0
  let rest := terms.filterMap (fun e =>
    match e with
    | .rat _ => none
    | _ => some e)
  if const == 0 then
    rest
  else .rat const :: rest


def normalize_mul_factors (factors : List Expr) : List Expr :=
  if factors.any (fun e => e == .rat 0) then
    [.rat 0]
  else
    let const := factors.foldl (fun acc e =>
      match e with
      | .rat q => acc * q
      | _ => acc) 1
    let rest := factors.filterMap (fun e =>
      match e with
      | .rat _ => none
      | _ => some e)
    if const == 1 then
      rest
    else
      .rat const :: rest



-- def mk_add (a b : Expr) : Expr :=
--   match a, b with
--   | .rat 0,      e => e
--   |      e, .rat 0 => e
--   | .rat m, .rat n => .rat (m + n)
--   |      _,      _ => .add a b

def mk_add (a b : Expr) : Expr :=
  from_add_terms (normalize_add_terms (add_terms a ++ add_terms b))

-- def mk_mul (a b : Expr) : Expr :=
--   match a, b with
--   | .rat 0,      _ => .rat 0
--   |      _, .rat 0 => .rat 0
--   | .rat 1,      e => e
--   |      e, .rat 1 => e
--   | .rat m, .rat n => .rat (m * n)
--   |      _,      _ => .mul a b

def mk_mul (a b : Expr) : Expr :=
  from_mul_factors (normalize_mul_factors (mul_factors a ++ mul_factors b))

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
