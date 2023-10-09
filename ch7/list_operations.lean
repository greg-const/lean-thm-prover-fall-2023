import data.nat.basic
namespace hidden

inductive list (α : Type*)
| nil {} : list
| cons : α → list → list

namespace list

notation (name := list)  `[` l:(foldr `,` (h t, cons h t) nil) `]` := l

variable {α : Type*}

notation (name := cons) h :: t  := cons h t

def append (s t : list α) : list α :=
list.rec_on s t (λ x l u, x::u)

notation (name := append) s ++ t := append s t

theorem nil_append (t : list α) : nil ++ t = t := rfl

theorem cons_append (x : α) (s t : list α) : x::s ++ t = x::(s ++ t) := rfl


theorem k (t0 : α) (l1 l2 : list α): (l1 = l2) → (t0::l1 = t0::l2) := 
begin
intro h,
rw h,
end


-- BEGIN
theorem append_nil (t : list α) : t ++ nil = t := 
begin
induction t with c hc,
rw append,

apply k,
apply t_ih,
end

theorem append_assoc (r s t : list α) :
  r ++ s ++ t = r ++ (s ++ t) := 
  begin
  induction r with c hc,
  apply nil_append,

  apply k,
  apply r_ih,
  end
-- END

def length : list α →  ℕ
| nil := 0
| (cons a t) := 1 + length t



theorem eq_list_eq_length (s t : list α) (h : s = t) : s.length = t.length :=
begin
induction s with c hc,
rw length,
have j : (t=nil),
begin
rw h,
end,
rw j,
rw length,

have m : (t=c::hc),
begin
rw h,
end,
rw h,
end

theorem length_sum (s t : list α) : length (s++t) = length s + length t :=
begin
induction s with c hc,
have j : (nil++t = t),
begin
apply nil_append
end,
rw j,
rw length,
rw zero_add, -- imported data.nat.basic to get this

rw length at *,
rw append at *,
rw length,
rw s_ih,
rw add_assoc,
end

#eval length [1, 2, 3, 4, 5]

end list


end hidden

-- try it https://leanprover-community.github.io/lean-web-editor/#code=namespace%20hidden%0Ainductive%20bool%20%3A%20Type%0A%7C%20ff%20%3A%20bool%0A%7C%20tt%20%3A%20bool%0A%0A--%20BEGIN%0Adef%20band%20%28b1%20b2%20%3A%20bool%29%20%3A%20bool%20%3A%3D%0Abool.cases_on%20b1%20hidden.bool.ff%20b2%0A%0Adef%20bor%20%28b1%20b2%20%3A%20bool%29%20%3A%20bool%20%3A%3D%0Abool.cases_on%20b1%20b2%20hidden.bool.tt%0A%0Adef%20bnot%20%28b1%20%3A%20bool%29%20%3A%20bool%20%3A%3D%0Abool.cases_on%20b1%20hidden.bool.tt%20hidden.bool.ff%0A--%20END%0A%0Adef%20bt1%20%3A%20bool%20%3A%3D%20hidden.bool.tt%0Adef%20bt2%20%3A%20bool%20%3A%3D%20hidden.bool.tt%0Adef%20bf1%20%3A%20bool%20%3A%3D%20hidden.bool.ff%0A%0A--%23reduce%0A%0A%23eval%20band%20bt1%20bf1%0A%23eval%20bor%20bf1%20bf1%0A%23eval%20bnot%20bt1%0A%0A%0A%0Aend%20hidden

