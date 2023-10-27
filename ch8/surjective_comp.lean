import tactic
open function

#print surjective

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}
open function
lemma surjective_comp {g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) :
surjective (g ∘ f) := 
begin
  -- We want to show that for every c in γ, there exists an a in α such that g(f(a)) = c.
  rintros c,
  -- Use the surjectivity of g to find some b in β such that g(b) = c.
  obtain ⟨b, hb⟩ := hg c,
  -- Use the surjectivity of f to find some a in α such that f(a) = b.
  obtain ⟨a, ha⟩ := hf b,
  -- Now, we show that g(f(a)) = c.
  use a,
  rw ←hb,
  rw ←ha,
end

lemma surjective_comp2{g : β → γ} {f : α → β}
  (hg : surjective g) (hf : surjective f) :
surjective (g ∘ f) := 
begin
rw surjective at *,
rw function.comp,

intro b,

have hg_on_b : (∃ c : β, g c = b) :=
begin
apply hg b,
end,

have two : (∃ a : α, g (f a) = b) :=
begin
cases hg_on_b with c hc,
cases hf c with a ha,
use a,
rw ha,
rw hc,
end,
apply two,

end
