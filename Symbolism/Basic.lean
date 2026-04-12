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

def expr_size : Expr → Nat
  | .rat _ => 1
  | .var _ => 1
  | .add a b => expr_size a + expr_size b + 1
  | .mul a b => expr_size a + expr_size b + 1
  | .pow a b => expr_size a + expr_size b + 1

def expr_rank : Expr → Nat
  | .rat _   => 0
  | .var _   => 1
  | .pow _ _ => 2
  | .mul _ _ => 3
  | .add _ _ => 4

def compare_rat (a b : Rat) : Ordering :=
  if a < b then .lt else if a == b then .eq else .gt

def compare_lex (first : Ordering) (rest : Unit → Ordering) : Ordering :=
  match first with
  | .eq => rest ()
  | other => other

def compare_expr : Expr → Expr → Ordering
  | .rat a, .rat b => compare_rat a b
  | .var a, .var b => compare a b
  | .pow a b, .pow c d => compare_lex (compare_expr a c) (fun _ => compare_expr b d)
  | .mul a b, .mul c d => compare_lex (compare_expr a c) (fun _ => compare_expr b d)
  | .add a b, .add c d => compare_lex (compare_expr a c) (fun _ => compare_expr b d)
  | a, b => compare (expr_rank a) (expr_rank b)
termination_by a b => expr_size a + expr_size b
decreasing_by all_goals simp [expr_size]; omega

def expr_le (a b : Expr) : Bool :=
  compare_expr a b != .gt

def insert_sorted_by {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys =>
      if le x y then
        x :: y :: ys
      else
        y :: insert_sorted_by le x ys

def sort_by {α : Type} (le : α → α → Bool) (xs : List α) : List α :=
  xs.foldr (insert_sorted_by le) []

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

def base_exp : Expr → Expr × Rat
  | .pow base (.rat exp) => (base, exp)
  | e                    => (e   , 1  )

def insert_factor (base : Expr) (exp : Rat) : List (Expr × Rat) → List (Expr × Rat)
  | [] =>
      if exp == 0 then [] else [(base, exp)]
  | (b, e) :: rest =>
      if b == base then
        let new_exp := e + exp
        if new_exp == 0 then rest else (b, new_exp) :: rest
      else
        (b, e) :: insert_factor base exp rest

def combine_factors (factors : List Expr) : List (Expr × Rat) :=
  factors.foldl (fun acc e =>
    let (base, exp) := base_exp e
    insert_factor base exp acc) []

def factor_power_le (a b : Expr × Rat) : Bool :=
  expr_le a.1 b.1

def sort_factor_powers (items : List (Expr × Rat)) : List (Expr × Rat) :=
  sort_by factor_power_le items

def factor_expr (base : Expr) (exp : Rat) : Expr :=
  mk_pow base (.rat exp)

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
    let combined :=
      (sort_factor_powers (combine_factors rest)).map
        (fun (base, exp) => factor_expr base exp)
    if const == 1 then
      combined
    else
      .rat const :: combined

def normalize_product (e : Expr) : Expr :=
  from_mul_factors (normalize_mul_factors (mul_factors e))

def coeff_term (e : Expr) : Rat × Expr :=
  let factors := mul_factors e
  let coeff := factors.foldl (fun acc factor =>
    match factor with
    | .rat q => acc * q
    | _ => acc) 1
  let rest := factors.filterMap (fun factor =>
    match factor with
    | .rat _ => none
    | _ => some factor)
  (coeff, normalize_product (from_mul_factors rest))

def insert_term (coeff : Rat) (term : Expr) : List (Rat × Expr) → List (Rat × Expr)
  | [] =>
      if coeff == 0 then [] else [(coeff, term)]
  | (c, t) :: rest =>
      if t == term then
        let new_coeff := c + coeff
        if new_coeff == 0 then rest else (new_coeff, t) :: rest
      else
        (c, t) :: insert_term coeff term rest

def combine_terms (terms : List Expr) : List (Rat × Expr) :=
  terms.foldl (fun acc e =>
    let (coeff, term) := coeff_term e
    insert_term coeff term acc) []

def term_le (a b : Rat × Expr) : Bool :=
  expr_le a.2 b.2

def sort_terms (items : List (Rat × Expr)) : List (Rat × Expr) :=
  sort_by term_le items

def term_expr (coeff : Rat) (term : Expr) : Expr :=
  if term == .rat 1 then
    .rat coeff
  else if coeff == 1 then
    term
  else
    normalize_product (.mul (.rat coeff) term)

def normalize_add_terms (terms : List Expr) : List Expr :=
  (sort_terms (combine_terms terms)).map
    (fun (coeff, term) => term_expr coeff term)

def mk_add (a b : Expr) : Expr :=
  from_add_terms (normalize_add_terms (add_terms a ++ add_terms b))

def mk_mul (a b : Expr) : Expr :=
  normalize_product (.mul a b)

def simplify : Expr -> Expr
  | .rat n => .rat n
  | .var x => .var x
  | .add a b => mk_add (simplify a) (simplify b)
  | .mul a b => mk_mul (simplify a) (simplify b)
  | .pow a b => mk_pow (simplify a) (simplify b)

end Expr
