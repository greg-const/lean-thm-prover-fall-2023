import Mathlib.Tactic

theorem succ_mod_lt (a : Nat) ( b : Nat) : a % Nat.succ b < Nat.succ b := by
{
  have h : Nat.succ b > 0 := by {simp}
  exact Nat.mod_lt a h
}

def euclid_gcd (a : Nat) (b : Nat) : Nat :=
  match a, b with
  | m, 0 => m
  | x, Nat.succ l =>
    have : x % Nat.succ l < Nat.succ l := by {apply succ_mod_lt x l}
    euclid_gcd (Nat.succ l) (x % Nat.succ l)
termination_by euclid_gcd a b => b

#eval euclid_gcd 0 9 -- special case..
-- danger if not dealt with properly (can imply 0 divisors?)
#eval euclid_gcd 20 7 -- coprime
#eval euclid_gcd 24 36
#eval euclid_gcd 9 0




def n_is_gcd (n : Nat) (a : Nat) (b : Nat) : Prop := n ∣ a ∧ n ∣ b ∧
¬(∃(h : Nat), h ∣ a ∧ h ∣ b ∧ h > n)

theorem gcd_is_unique (x1 : Nat) (x2 : Nat) : ∀(a : Nat) (b : Nat), n_is_gcd x1 a b ∧ n_is_gcd x2 a b → (x1 = x2) := by
{
  intro a b
  intro h
  obtain ⟨x1_gcd, x2_gcd⟩ := h

  unfold n_is_gcd at x1_gcd
  obtain ⟨x1_div_a, x1_div_b, x1_gcd⟩ := x1_gcd
  simp at x1_gcd

  unfold n_is_gcd at x2_gcd
  obtain ⟨x2_div_a, x2_div_b, x2_gcd⟩ := x2_gcd
  simp at x2_gcd

  have x2_leq_x1 : x2 ≤ x1 := by {apply x1_gcd x2 x2_div_a x2_div_b}
  have x1_leq_x2 : x1 ≤ x2 := by {apply x2_gcd x1 x1_div_a x1_div_b}

  exact Nat.le_antisymm (x1_leq_x2) (x2_leq_x1)
}

theorem r_n_gcd : n_is_gcd (Nat.succ m) (Nat.succ m) 0 := by
{
  rw [n_is_gcd]

  constructor
  simp
  constructor
  simp

  intro contra
  cases' contra with w h1
  obtain ⟨hw_m, _, w_gt_m⟩ := h1


  have : w ≤ Nat.succ m := by {apply Nat.le_of_dvd (by simp) hw_m}
  linarith
}

theorem step  : (n_is_gcd n a b) ↔ (n_is_gcd n b (a % b)) := by
{
  constructor
  { -- step forward
    intro ev
    cases' ev with h1 r
    cases' r with h2 h3

    unfold n_is_gcd
    constructor
    exact h2
    constructor
    exact (Nat.dvd_mod_iff h2).mpr h1

    intro contra
    cases' contra with x h9
    cases' h9 with x_div_b right
    cases' right with x_div_r x_gt_n

    have h4 : x ∣ a := by {exact (Nat.dvd_mod_iff x_div_b).mp x_div_r}

    apply h3
    use x
  }
  { -- step back
    intro ev
    unfold n_is_gcd at ev
    obtain ⟨n_div_b, n_div_a, n_gcd⟩ := ev
    unfold n_is_gcd
    constructor
    { -- n divides a
      exact (Nat.dvd_mod_iff n_div_b).mp n_div_a
    }
    {
      constructor ;{assumption} -- n divides b
      intro contra
      cases' contra with x h1
      obtain ⟨x_div_a, x_div_b, x_gt_n⟩ := h1

      apply n_gcd
      use x
      constructor
      · exact x_div_b
      constructor
      · exact (Nat.dvd_mod_iff x_div_b).mpr x_div_a
      exact x_gt_n
    }

  }
}

theorem euclid_gcd_step (a : Nat) (b : Nat) : (b > 0) → euclid_gcd a b = euclid_gcd b (a % b) :=
by
{
  --intro a_gt_b b_pos
  intro b_pos
  have b_eq_succ: b=Nat.succ (Nat.pred b) := by {exact (Nat.succ_pred_eq_of_pos b_pos).symm}
  --have a_eq_succ : a = Nat.succ (Nat.pred a) := by {have : a>0 := by {exact Nat.zero_lt_of_lt a_gt_b}; exact (Nat.succ_pred_eq_of_pos this).symm}
  cases' a with n
  simp
  simp_rw [euclid_gcd]
  unfold euclid_gcd
  rw [b_eq_succ]
  simp
  rw [←b_eq_succ]
  unfold euclid_gcd
  rfl
  conv => left; unfold euclid_gcd; rw [b_eq_succ]; simp
  rw [←b_eq_succ]
}

theorem euclid_gcd_is_gcd_a_b_iff_euclid_gcd_b_a_mod_b_is_gcd_a_b (a : Nat) (b : Nat) : n_is_gcd (euclid_gcd a b) a b ↔ n_is_gcd (euclid_gcd b (a % b)) a b := by
{
  induction' a with n n_ih
  { -- a is 0
    simp
    rw [euclid_gcd]
    cases' b with bp
    { -- a and b are 0
      simp
      rw [euclid_gcd]
    }
    { -- a 0, b non-0
      simp_rw [euclid_gcd]
      simp
      rfl
    }
  }
  { -- a non-zero
    induction' b with bp
    { -- b zero
      simp
      simp_rw [euclid_gcd]
      simp
      rfl
    }
    { -- a and b non-zero
      rfl
    }
  }
}

theorem euclid_gcd_is_gcd_a_b_iff_euclid_gcd_b_a_mod_b_is_gcd_b_a_mod_b (a : Nat) (b : Nat) : n_is_gcd (euclid_gcd a b) a b ↔ n_is_gcd (euclid_gcd b (a % b)) b (a%b):= by
{
  induction' a with as as_ih
  { -- a is 0
    simp
    rw [euclid_gcd]
    cases' b with bp
    { -- a and b are 0
      simp
      rw [euclid_gcd]
    }
    { -- a 0, b non-0
      simp_rw [euclid_gcd]
      simp
      simp_rw [euclid_gcd]
      constructor
      intro h
      exact step.mp h -- step.mp = step forward
      intro _
      exact step.mp r_n_gcd
    }
  }
  { -- a non-zero
    induction' b with bp _
    { -- b zero
      simp
      simp_rw [euclid_gcd]
      simp
      simp_rw [euclid_gcd]
      constructor
      simp [step.mp, r_n_gcd]
      exact step.mp r_n_gcd
      intro h
      exact step.mp h
    }
    { -- a and b non-zero
      constructor
      intro h
      simp_rw [euclid_gcd] at h
      apply step.mp
      assumption

      intro h
      apply step.mpr
      simp_rw [euclid_gcd]
      assumption
    }
  }
}
theorem combine_step (a : Nat) (b : Nat) : n_is_gcd (euclid_gcd a b) a b ↔ n_is_gcd (euclid_gcd b (a % b)) b (a%b) := by {exact euclid_gcd_is_gcd_a_b_iff_euclid_gcd_b_a_mod_b_is_gcd_b_a_mod_b a b}


theorem k : (n_is_gcd 3 6 9) := by
{
  unfold n_is_gcd
  simp
  intro x
  intro m
  intro y
  cases' x with k
  simp

  let l := Nat.succ k
  have hL : (Nat.succ k = l) := by rfl -- quick rename
  rw [hL] at m y
  rw [hL]

  have l_leq_6 : (l ≤ 6) := by {exact Nat.le_of_dvd (by simp) m}

  have l_ne_4_5_6_impl : (l ≠ 4 ∧ l ≠ 5 ∧ l ≠ 6 → l ≤ 3) := by
  {
    intro h1
    cases' h1 with ne4 th
    cases' th with ne5 ne6
    interval_cases l
    simp
    simp
    simp
    simp
    exact (ne4 rfl).elim
    exact (ne5 rfl).elim
    exact (ne6 rfl).elim
  }
  have l_ne_4 : l ≠ 4 := by { intro hl; rw [hl] at m; norm_num at m }
  have l_ne_5 : l ≠ 5 := by { intro hl; rw [hl] at m; norm_num at m }
  have l_ne_6 : l ≠ 6 := by { intro hl; rw [hl] at y; norm_num at y }

  exact l_ne_4_5_6_impl ⟨l_ne_4, l_ne_5, l_ne_6⟩
}

def coprime_iff_gcd_1 (a : Nat) (b : Nat) (ev : b > 0)
:
(∀h, h ∣ a ∧ h ∣ b → h = 1) ↔ (n_is_gcd 1 a b) := by
{
  constructor
  intro h1
  unfold n_is_gcd
  constructor; simp; constructor; simp; simp
  intro x
  have : x ∣ a ∧ x ∣ b → x = 1 := by {apply h1 x}
  intro h h2
  have : x=1 := by {exact this ⟨h, h2⟩}
  linarith

  intro h1
  unfold n_is_gcd at h1
  obtain ⟨_, _, h3⟩ := h1

  intro x
  intro ⟨x_div_a, x_div_b⟩
  simp at h3
  have : x ≤ 1 := by {exact h3 x x_div_a x_div_b}
  have quick (n : Nat) (ev : b > 0) : (n ∣ b → n > 0) := by
  {exact fun a_1 => Nat.pos_of_dvd_of_pos a_1 ev}
  have x_geq_0 : x > 0 := by {exact quick x ev x_div_b}
  linarith
}



theorem euclid_alg_works : ∀(a : Nat) (b : Nat) (_ : (a > b)) (_ : b > 0),  n_is_gcd (euclid_gcd a b) a b := by
{
  intro a b a_gt_b b_gt_0

  have a_gt_0 : a > 0 := by {exact Nat.zero_lt_of_lt a_gt_b}

  apply Nat.case_strong_induction_on b

  simp_rw [euclid_gcd]
  have a_ex : a = Nat.succ (Nat.pred a) := by {exact (Nat.succ_pred_eq_of_pos a_gt_0).symm}
  rw [a_ex]
  exact r_n_gcd

  intro n
  intro h


  have : n_is_gcd (euclid_gcd (Nat.succ n) (a % Nat.succ n)) (Nat.succ n) (a % Nat.succ n) :=
    by
    {
      have : a % (Nat.succ n) ≤ n := by {exact Nat.lt_succ.mp (succ_mod_lt a n)}
      have t : n_is_gcd (euclid_gcd a (a % Nat.succ n)) a (a % Nat.succ n) := by {apply h (a % Nat.succ n); assumption}

      apply (combine_step (a) (Nat.succ n)).mp

      refine step.mpr ?_

      have j : a % Nat.succ n = 0 ∨ a % Nat.succ n > 0 := by {exact Nat.eq_zero_or_pos (a % Nat.succ n)}
      cases' j with div ndiv
      rw [div]
      rw [div] at t
      simp_rw [euclid_gcd]
      rw [div]
      simp_rw [euclid_gcd]
      unfold n_is_gcd
      constructor; simp; constructor; simp; intro contra; cases' contra with x h
      obtain ⟨x_div_n, _, x_gt_n⟩ := h
      have x_leq_n : x ≤ Nat.succ n := by {exact Nat.le_of_dvd (by simp) x_div_n}
      linarith
      /-
      ab: ℕ
      a_gt_b: a > b
      b_gt_0: b > 0
      a_gt_0: a > 0
      n: ℕ
      h: ∀ (m : ℕ), m ≤ n → n_is_gcd (euclid_gcd a m) a m
      this: a % Nat.succ n ≤ n
      t: n_is_gcd (euclid_gcd a (a % Nat.succ n)) a (a % Nat.succ n)
      ndiv: a % Nat.succ n > 0
      ⊢ n_is_gcd (euclid_gcd a (Nat.succ n)) (Nat.succ n) (a % Nat.succ n)
      -/
      sorry
      /-have lowest (v1 : Nat) (v2 : Nat) : ∃v3, euclid_gcd v1 v2 = euclid_gcd v3 0 := by
      {
        sorry
      }

      have lowest_is_ans (v1 : Nat) (v2 : Nat) : ∃v3, euclid_gcd v1 v2 = euclid_gcd v3 0 → n_is_gcd v3 v1 v2 := by
      {
        sorry
      }


      have : ∃ m, euclid_gcd a (Nat.succ n) = euclid_gcd m 0 := by
      {apply lowest a (Nat.succ n)}

      have this_save := this
      {
        cases' this with r_n h_r_n
        rw [h_r_n]
        simp_rw [euclid_gcd]
        have :  n_is_gcd r_n a (Nat.succ n) := by {}
      }

      --extract_goal
      --refine equiv (Nat.succ n) (a % Nat.succ n) ?_ ?_



      have : (n_is_gcd (euclid_gcd a (Nat.succ n)) (Nat.succ n) (a % Nat.succ n)) := by
      {

        unfold n_is_gcd
        constructor


      }

      exfalso

      exact succ_mod_lt a n
      exact ndiv-/
    }


  exact step.mpr this
}


theorem n_is_gcd_iff_euclid :∀(a : Nat) (b : Nat) (x : Nat) (_ : a > b) (_ : b > 0),  n_is_gcd x a b ↔ (euclid_gcd a b = x) := by
{
  intro a b x a_gt_b b_gt_0
  constructor
  {
    intro x_is_gcd
    have : n_is_gcd (euclid_gcd a b) a b := by {apply euclid_alg_works a b a_gt_b b_gt_0}
    exact Eq.symm (gcd_is_unique x (euclid_gcd a b) a b ⟨x_is_gcd, this⟩)
  }
  {
    intro h
    rw [←h]
    apply euclid_alg_works
    assumption
    assumption
  }

}

#check euclid_alg_works 8 2 (by simp)

def x : n_is_gcd 2 8 6 := ((n_is_gcd_iff_euclid _ _ _ (by simp) (by simp)).mpr) (rfl)
