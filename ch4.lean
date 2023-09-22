-- Ch 4 ex 1 
variables (α : Type*) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  iff.intro
  (
    assume h : (∀ x, p x ∧ q x),
    and.intro
      (assume y : α,
      show p y, from (h y).left)
      (assume x : α,
      show q x, from (h x).right)
  )

  (
    assume h : (∀ x, p x) ∧ (∀ x, q x),
    assume y : α,
    and.intro
      (show p y, from (h.left y))
      (show q y, from (h.right y))
  )


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
  assume h : (∀ x, p x) ∨ (∀ x, q x),
  assume y : α, 
  or.elim h 
  (
  assume hl : (∀ x, p x),
  or.inl (show p y, from hl y)
  )
  (
  assume hr : (∀ x, q x),
  or.inr (show q y, from hr y)
  )

