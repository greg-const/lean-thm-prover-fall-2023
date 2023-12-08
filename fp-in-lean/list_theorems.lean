
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
