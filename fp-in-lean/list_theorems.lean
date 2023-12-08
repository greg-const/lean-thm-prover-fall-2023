
#check List Nat
#check List.append


def sum_list (l : List Nat) (counter : Nat) : Nat :=
match l with
| [] => counter
| h :: t => sum_list t (h + counter)

--def k := List Nat

theorem nil_append (ls : List Nat) : List.length (List.append ls []) = List.length (List.append [] ls) := by
{
    induction ls with
    | nil => {rfl}
    | cons => {simp [List.append]}
}

theorem append_length_comm (a b : List Nat) : List.length (List.append a b) = List.length (List.append b a) := by
{
  induction a with
  | nil => {simp}
  | cons head tail tail_ih => {
    simp only [List.append, List.length]
    rw [tail_ih]
    simp
    rfl
  }
}

theorem list_thm (ls1 : List Nat) (ls2 : List Nat) :
(List.append ls1 ls2).length = (List.append ls2 ls1).length := by
{
  induction ls1 with
  | nil => {
    induction ls2 with
    | nil => {rfl}
    | cons => {simp [List.append]}
  }
  | cons => {
    rename_i tail_ih
    rename_i tail
    rename_i head

    induction ls2 with
    | nil => {rw [nil_append]}
    | cons => {apply append_length_comm}
  }
}



def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs


def Tail.sumHelper (soFar : Nat) : List Nat → Nat
| [] => soFar
| x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs



theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n ; rfl
  | cons y ys ih => {
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n+y)
  }

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys =>
    {
      simp [NonTail.sum, Tail.sum, Tail.sumHelper]
      exact non_tail_sum_eq_helper_accum ys y
    }
