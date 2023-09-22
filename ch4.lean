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
