variables {p q r s: Prop}


-- section of Ch 3 Exercise 1 
-- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p :=
    iff.intro
      (assume h: p ∧ q, and.intro h.right h.left)
      (assume h: q ∧ p, and.intro h.right h.left)


  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    iff.intro
      (assume h: (p ∧ q) ∧ r, ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
      (assume h: p ∧ (q ∧ r), ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    iff.intro
      (assume h: (p ∨ q) ∨ r, or.elim h
        (assume hpq: p ∨ q, or.elim hpq
          (assume hp: p, or.inl hp)
          (assume hq: q, or.inr (or.inl hq)))
        (assume hr: r, or.inr (or.inr hr)))
      (assume h: p ∨ (q ∨ r), or.elim h
        (assume hp: p, or.inl (or.inl hp))
        (assume hqr: q ∨ r, or.elim hqr
          (assume hq: q, or.inl (or.inr hq))
          (assume hr: r, or.inr hr)))

-- Ch 3 Exercise 1 Done in tactic mode 
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
split,
intro h,
cases h with pr qr,
cases pr with pr1 pr2,
left,apply pr1,
right, left, apply pr2,
right, right, apply qr,

intro h,
cases h with p qr,
left, left, apply p,
cases qr with qr1 qr2,
left, right, apply qr1,
right, apply qr2,
end

example : p ∧ q ↔ q ∧ p :=
begin
split,
intro h,
split,
apply h.right,
apply h.left,

intro h1,
split,
apply h1.right,
apply h1.left,
end

--- Better braces usage:

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  { 
    intro h,
    cases h.right with hq hr,
    { show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨h.left, hq⟩ },
    { show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨h.left, hr⟩ }
  },
  {
    intro h,  
    cases h with hpq hpr,
    { show p ∧ (q ∨ r), from ⟨hpq.left, or.inl hpq.right⟩ },
    { show p ∧ (q ∨ r), from ⟨hpr.left, or.inr hpr.right⟩ }
  }
end


