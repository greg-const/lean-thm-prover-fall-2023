namespace hidden

inductive nat : Type
| zero : nat
| succ : nat → nat

namespace nat

-- BEGIN
def add : nat → nat → nat
| m zero     := m
| m (succ n) := succ (add m n)

local infix (name := add) ` + ` := add

theorem add_zero (m : nat) : m + zero = m := rfl
theorem add_succ (m n : nat) : m + succ n = succ (m + n) := rfl

theorem zero_add : ∀ n, zero + n = n
| zero     := rfl
| (succ n) := -- congr_arg succ (zero_add n)
begin
rw add,
rw zero_add,
end


#check congr_arg succ

def mul : nat → nat → nat
| n zero     := zero
| n (succ m) := mul n m + n
-- END

end nat
end hidden
