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
