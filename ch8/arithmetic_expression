inductive aexpr : Type
| const : ℕ → aexpr
| var : ℕ → aexpr
| plus : aexpr → aexpr → aexpr
| times : aexpr → aexpr → aexpr

open aexpr

def sample_aexpr : aexpr :=
plus (times (var 0) (const 7)) (times (const 2) (var 1))

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
#eval aeval sample_val sample_aexpr
-- END


-- BEGIN
def simp_const : aexpr → aexpr
| (plus (const n₁) (const n₂))  := const (n₁ + n₂)
| (times (const n₁) (const n₂)) := const (n₁ * n₂)
| e                             := e

def fuse : aexpr → aexpr 
| (times e₁ e₂) := times  (fuse e₁) (fuse e₂)
| (plus e₁ e₂) := plus (fuse e₁) (fuse e₂)
| e                             := simp_const e
-- how to do this otherwise?

theorem simp_const_eq (v : ℕ → ℕ) :
  ∀ e : aexpr, aeval v (simp_const e) = aeval v e :=
begin
  intro e,
  induction e with _ _ a b _ _ a b _ _,
  { refl },
  { refl },
  { cases a,
    cases b,
    { refl },
    { refl },
    { refl },
    { refl },
    { refl },
    { refl },
    { refl } },
  { cases a,
    cases b,
    { refl },
    { refl },
    { refl },
    { refl },
    { refl },
    { refl },
    { refl },
  }
end
theorem simp_const_eq_faster (v : ℕ → ℕ) :
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
induction e with _ _ a b _ _  a b _ _,
{refl,},
{refl,},
{ cases a,
  cases b,
  {refl,},
  {refl,},
  {rw fuse, rw aeval, rw e_ih_ᾰ_1, refl,},
  {rw fuse, rw aeval, rw e_ih_ᾰ_1, refl,},
  {simp [fuse, aeval, simp_const, e_ih_ᾰ_1, e_ih_ᾰ],},
  {rw fuse, rw aeval, rw e_ih_ᾰ, simp [fuse, aeval, simp_const, e_ih_ᾰ, e_ih_ᾰ_1], },
  {rw fuse, rw aeval, rw e_ih_ᾰ, simp [fuse, aeval, simp_const, e_ih_ᾰ_1, e_ih_ᾰ], },
},
{ cases a,
  cases b,
  {refl,},
  {refl,},
  {rw fuse, rw aeval, rw e_ih_ᾰ_1, refl,},
  {rw fuse, rw aeval, rw e_ih_ᾰ_1, refl,},
  {simp [fuse, aeval, simp_const, e_ih_ᾰ_1, e_ih_ᾰ],},
  {rw fuse, rw aeval, rw e_ih_ᾰ, simp [fuse, aeval, simp_const, e_ih_ᾰ_1, e_ih_ᾰ], },
  {rw fuse, rw aeval, rw e_ih_ᾰ, simp [fuse, aeval, simp_const, e_ih_ᾰ_1, e_ih_ᾰ], },
}



end
-- END

