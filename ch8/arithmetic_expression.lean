inductive aexpr : Type
| const : ℕ → aexpr
| var : ℕ → aexpr
| plus : aexpr → aexpr → aexpr
| times : aexpr → aexpr → aexpr

open aexpr

def sample_aexpr : aexpr := 
times (plus (times (var 0) (const 7)) (times (const 2) (var 1))) (const 2)

-- BEGIN
def aeval (v : ℕ → ℕ) : aexpr → ℕ
| (const n)    := n
| (var n)      := v n
| (plus e₁ e₂)  := aeval e₁ + aeval e₂ 
| (times e₁ e₂) := aeval e₁ * aeval e₂ 

def sample_val : ℕ → ℕ
| 0 := 5
| 1 := 6
| _ := 0

-- Try it out. You should get 47 here.
#eval sample_aexpr
#eval aeval sample_val sample_aexpr
-- END

def to_str : aexpr → string
| (const n)    := to_string n
| (var n)      := "var" ++ to_string n
| (plus e₁ e₂)    := to_str e₁ ++ " + " ++ to_str e₂ 
| (times e₁ e₂) := "(" ++ to_str e₁ ++ ") * " ++ "(" ++ to_str e₂ ++ ")" 

instance aexpr_has_repr : has_repr aexpr := has_repr.mk (to_str)
#eval sample_aexpr

-- BEGIN
def simp_const : aexpr → aexpr
| (plus (const n₁) (const n₂))  := const (n₁ + n₂)
| (times (const n₁) (const n₂)) := const (n₁ * n₂)
| e                             := e

def fuse : aexpr → aexpr 
| (plus (const n₁) (const n₂))  := const (n₁ + n₂)
| (times (const n₁) (const n₂)) := const (n₁ * n₂)
| (times e₁ e₂) := simp_const (times  (fuse e₁) (fuse e₂))
| (plus e₁ e₂) := simp_const (plus (fuse e₁) (fuse e₂))
| e                             := simp_const e
-- how to do this otherwise?

def sample_redundant_consts : aexpr := 
plus (const 5) (const 7)

def sample_redundant_expr : aexpr :=

plus (times ( plus (const 1) (const 2) ) (var 1) ) ( times (const 8) (const 3))

def sample_more_redundant_expr : aexpr := 
plus(
  times 
  (times (plus (const 5) (const 7)) (var 0)) (times (const 3) (const 2))
  )
  (plus (plus (plus (const 3) (const 5)) (const 6)) (const 10))

#eval sample_redundant_consts
#eval simp_const sample_redundant_consts -- 12

#eval sample_redundant_expr
#eval simp_const sample_redundant_expr -- does nothing
#eval fuse sample_redundant_expr -- i think this follows specification 

#eval sample_more_redundant_expr
#eval fuse sample_more_redundant_expr




theorem simp_const_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (simp_const e) = aeval v e :=
  begin
  intro e,

  induction e with c n e1 e2 h3 h4 h5 h6 h7 h8,
  rw simp_const,
  rw simp_const,

  cases e1,
  cases e2,
  repeat {rw simp_const},
  repeat {rw aeval},
  
  cases h5,
  cases h6,
  repeat {rw simp_const},
  repeat {rw aeval},
  end
theorem fuse_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (fuse e) = aeval v e :=
begin
intro e,
induction e with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13,
refl,
refl,

cases h3,
cases h4,
repeat {simp [simp_const_eq, fuse, simp_const, aeval, h6, h5]},

cases h7,
cases h8,
repeat {simp [simp_const_eq, fuse, simp_const, aeval, h9, h10]},

end
-- END

