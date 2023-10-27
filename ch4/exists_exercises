import tactic
open classical

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : (∃ x : α, r) → r := begin
intro h1,
cases h1 with x hx,
exact hx,
end
example (a : α) : r → (∃ x : α, r) := begin
intro h1,
use a,
exact h1,
end
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := begin
apply iff.intro,
intro h1,
cases h1 with x hx,
use x,
exact hx.left,
exact hx.right,

intro h2,
cases h2.left with x hx,
use x, 
exact ⟨hx, h2.right⟩,
end

variables (α : Type*) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x : α, r) ↔ r) := 
begin
intro h1,
apply iff.intro,
intro h2,
exact h2 h1,
intro h3,
intro h4,
exact h3,
end

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
begin
apply iff.intro,
intro h1,
by_cases hr : r,
apply or.inr hr,
left,
intro x,
specialize h1 x,
cases h1 with hp hr,
assumption,
contradiction,


intro h1,
intro x,
cases h1 with hpx hr2,
specialize hpx x,
left,
exact hpx,
right, 
exact hr2,

end

