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

-- try it https://leanprover-community.github.io/lean-web-editor/#code=import%20data.nat.basic%0Anamespace%20hidden%0A%0Ainductive%20list%20%28%CE%B1%20%3A%20Type*%29%0A%7C%20nil%20%7B%7D%20%3A%20list%0A%7C%20cons%20%3A%20%CE%B1%20%E2%86%92%20list%20%E2%86%92%20list%0A%0Anamespace%20list%0A%0Anotation%20%28name%20%3A%3D%20list%29%20%20%60%5B%60%20l%3A%28foldr%20%60%2C%60%20%28h%20t%2C%20cons%20h%20t%29%20nil%29%20%60%5D%60%20%3A%3D%20l%0A%0Avariable%20%7B%CE%B1%20%3A%20Type*%7D%0A%0Anotation%20%28name%20%3A%3D%20cons%29%20h%20%3A%3A%20t%20%20%3A%3D%20cons%20h%20t%0A%0Adef%20append%20%28s%20t%20%3A%20list%20%CE%B1%29%20%3A%20list%20%CE%B1%20%3A%3D%0Alist.rec_on%20s%20t%20%28%CE%BB%20x%20l%20u%2C%20x%3A%3Au%29%0A%0Anotation%20%28name%20%3A%3D%20append%29%20s%20%2B%2B%20t%20%3A%3D%20append%20s%20t%0A%0Atheorem%20nil_append%20%28t%20%3A%20list%20%CE%B1%29%20%3A%20nil%20%2B%2B%20t%20%3D%20t%20%3A%3D%20rfl%0A%0Atheorem%20cons_append%20%28x%20%3A%20%CE%B1%29%20%28s%20t%20%3A%20list%20%CE%B1%29%20%3A%20x%3A%3As%20%2B%2B%20t%20%3D%20x%3A%3A%28s%20%2B%2B%20t%29%20%3A%3D%20rfl%0A%0A%0Atheorem%20k%20%28t0%20%3A%20%CE%B1%29%20%28l1%20l2%20%3A%20list%20%CE%B1%29%3A%20%28l1%20%3D%20l2%29%20%E2%86%92%20%28t0%3A%3Al1%20%3D%20t0%3A%3Al2%29%20%3A%3D%20%0Abegin%0Aintro%20h%2C%0Arw%20h%2C%0Aend%0A%0A%0A--%20BEGIN%0Atheorem%20append_nil%20%28t%20%3A%20list%20%CE%B1%29%20%3A%20t%20%2B%2B%20nil%20%3D%20t%20%3A%3D%20%0Abegin%0Ainduction%20t%20with%20c%20hc%2C%0Arw%20append%2C%0A%0Aapply%20k%2C%0Aapply%20t_ih%2C%0Aend%0A%0Atheorem%20append_assoc%20%28r%20s%20t%20%3A%20list%20%CE%B1%29%20%3A%0A%20%20r%20%2B%2B%20s%20%2B%2B%20t%20%3D%20r%20%2B%2B%20%28s%20%2B%2B%20t%29%20%3A%3D%20%0A%20%20begin%0A%20%20induction%20r%20with%20c%20hc%2C%0A%20%20apply%20nil_append%2C%0A%0A%20%20apply%20k%2C%0A%20%20apply%20r_ih%2C%0A%20%20end%0A--%20END%0A%0Adef%20length%20%3A%20list%20%CE%B1%20%E2%86%92%20%20%E2%84%95%0A%7C%20nil%20%3A%3D%200%0A%7C%20%28cons%20a%20t%29%20%3A%3D%201%20%2B%20length%20t%0A%0A%0A%0Atheorem%20eq_list_eq_length%20%28s%20t%20%3A%20list%20%CE%B1%29%20%28h%20%3A%20s%20%3D%20t%29%20%3A%20s.length%20%3D%20t.length%20%3A%3D%0Abegin%0Ainduction%20s%20with%20c%20hc%2C%0Arw%20length%2C%0Ahave%20j%20%3A%20%28t%3Dnil%29%2C%0Abegin%0Arw%20h%2C%0Aend%2C%0Arw%20j%2C%0Arw%20length%2C%0A%0Ahave%20m%20%3A%20%28t%3Dc%3A%3Ahc%29%2C%0Abegin%0Arw%20h%2C%0Aend%2C%0Arw%20h%2C%0Aend%0A%0Atheorem%20length_sum%20%28s%20t%20%3A%20list%20%CE%B1%29%20%3A%20length%20%28s%2B%2Bt%29%20%3D%20length%20s%20%2B%20length%20t%20%3A%3D%0Abegin%0Ainduction%20s%20with%20c%20hc%2C%0Ahave%20j%20%3A%20%28nil%2B%2Bt%20%3D%20t%29%2C%0Abegin%0Aapply%20nil_append%0Aend%2C%0Arw%20j%2C%0Arw%20length%2C%0Arw%20zero_add%2C%20--%20imported%20data.nat.basic%20to%20get%20this%0A%0Arw%20length%20at%20*%2C%0Arw%20append%20at%20*%2C%0Arw%20length%2C%0Arw%20s_ih%2C%0Arw%20add_assoc%2C%0Aend%0A%0A%23eval%20length%20%5B1%2C%202%2C%203%2C%204%2C%205%5D%0A%0Aend%20list%0A%0A%0Aend%20hidden
--
