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

end list

end hidden
