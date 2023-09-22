variables {p q r s: Prop}

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


  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=