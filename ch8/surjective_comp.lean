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
  rintros c,
  obtain ⟨b, hb⟩ := hg c,
  obtain ⟨a, ha⟩ := hf b,
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
