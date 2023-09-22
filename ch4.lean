import data.int.basic


-- Ch 4 Exercise 1
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


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry -- later done in ch 5 with tactics


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


-- Exercise 7. This is definitely not optimally written.

#check sub_self

example (x : ℤ) : x * 0 = 0 :=
begin
have t : (x-x)=0,
rw sub_self,

have m : 0=(x-x),
rw t,

rw m,
rw mul_sub,
rw sub_self,
rw sub_self,
end


