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
#eval euclid_gcd 20 7 -- coprime
#eval euclid_gcd 24 36
#eval euclid_gcd 9 0 -- special case ? This could be danger


theorem euc_gcd_ab_eq_gcd_ba (a : Nat) (b : Nat) : euclid_gcd a b = euclid_gcd b a := by
{
  cases' b with bs bs_ih
  simp_rw [euclid_gcd]
  cases' a with as as_ih
  simp
  simp_rw [euclid_gcd]
  simp; simp_rw [euclid_gcd]

  cases' a with as as_ih
  simp; simp_rw [euclid_gcd]; simp; simp_rw [euclid_gcd];

  have ord : (as > bs) ∨ (as ≤ bs) := by {exact Nat.lt_or_ge bs as}
  cases' ord with as_gt as_leq
  simp_rw [euclid_gcd];
  have suc_as_gt : Nat.succ as > Nat.succ bs := by {exact Nat.lt_succ.mpr as_gt}
  have bs_same_mod : Nat.succ bs % Nat.succ as = Nat.succ bs := by {exact Nat.mod_eq_of_lt suc_as_gt}

  rw [bs_same_mod]
  simp_rw [euclid_gcd]

  have ord : as = bs ∨ as < bs := by {exact Nat.eq_or_lt_of_le as_leq}
  cases' ord with as_eq_bs as_le
  rw [as_eq_bs]

  simp_rw [euclid_gcd]
  have suc_as_gt : Nat.succ as < Nat.succ bs := by {exact Nat.lt_succ.mpr as_le}
  have as_same_mod : Nat.succ as % Nat.succ bs = Nat.succ as := by {exact Nat.mod_eq_of_lt suc_as_gt}

  rw [as_same_mod]
  simp_rw [euclid_gcd];

}

--theorem euc_gcd_a_b_eq_gcd_aminusb_b {a : Nat} {b : Nat} (a_geq_b : a ≥ b) : euclid_gcd a b = euclid_gcd (a-b) b := by


def n_is_gcd (n : Nat) (a : Nat) (b : Nat) : Prop := n ∣ a ∧ n ∣ b ∧
¬(∃(h : Nat), h ∣ a ∧ h ∣ b ∧ h > n)

theorem gcd_ab_eq_gcd_ba {x : Nat} {a : Nat} {b : Nat} :  n_is_gcd x a b → n_is_gcd x b a := by
{
  intro h
  unfold n_is_gcd at h
  obtain ⟨x_div_a, x_div_b, x_gcd⟩ := h
  --simp at x_gcd
  unfold n_is_gcd
  constructor
  assumption
  constructor
  assumption
  simp at x_gcd
  simp
  intro n
  intro n_div_b
  intro n_div_a
  exact x_gcd n n_div_a n_div_b
}

theorem gcd_a_b_eq_gcd_aminusb_b {x : Nat} {a : Nat} {b : Nat} (ev : a ≥ b) : n_is_gcd x a b ↔ n_is_gcd x (a-b) b := by
{
  constructor
  intro h


  unfold n_is_gcd
  obtain ⟨x_div_a, x_div_b, x_gc⟩ := h
  constructor
  exact Nat.dvd_sub' x_div_a x_div_b
  constructor
  assumption
  intro contra; cases' contra with w wh
  obtain ⟨w_div_aminusb, w_div_b, w_gc⟩ := wh
  simp at x_gc
  have w_div_a : (w ∣ a) := by {
    have ch: ∃c, b = w*c := by {exact w_div_b}
    cases' ch with c ch

    have ch2: ∃c2, (a-b) = w*c2 := by {exact w_div_aminusb}
    cases' ch2 with c2 ch2
    rw [ch] at ch2
    cases' b with bs
    exact w_div_aminusb
    have s : _ := by {exact Nat.dvd_add w_div_aminusb w_div_b}
    rw [Nat.sub_add_cancel] at s
    assumption
    assumption
  }
  {
    exact Nat.le_lt_antisymm (x_gc w w_div_a w_div_b) w_gc
  }
  {
    unfold n_is_gcd
    intro h
    obtain ⟨x_div_aminusb, x_div_b, x_gc⟩ := h
    simp at x_gc
    constructor
    have b_leq_a: b ≤ a := by {exact ev}
    have a_minus_b_plus_b_eq_a : (a - b + b = a) := by {exact Nat.sub_add_cancel b_leq_a}
    have : x ∣ (a - b + b) := by {exact Nat.dvd_add x_div_aminusb x_div_b}
    rw [a_minus_b_plus_b_eq_a] at this
    assumption
    constructor
    assumption
    intro contra
    cases' contra with w wh; obtain ⟨w_div_a, w_div_b, w_gt_x⟩ := wh;

    have w_div_aminusb : (w ∣ a-b) := by {exact Nat.dvd_sub' w_div_a w_div_b }
    exact Nat.le_lt_antisymm (x_gc w w_div_aminusb w_div_b) w_gt_x
  }
}

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


theorem nat_sub (a : Nat) (b : Nat) : Nat.succ a - Nat.succ b < Nat.succ a := by
{
  induction' a with n _
  simp
  simp
  exact Nat.sub_lt_succ (n + 1) b
}

theorem euclid_alg_works : ∀(a : Nat) (b : Nat) (_ : (a > b)) (_ : b > 0),  n_is_gcd (euclid_gcd a b) a b := by
{
  intro a b a_gt_b b_gt_0

  have a_gt_0 : a > 0 := by {apply Nat.zero_lt_of_lt a_gt_b}

  induction b using Nat.case_strong_induction_on generalizing a

  have a_ex : a = Nat.succ (Nat.pred a) := by {exact Nat.eq_of_mul_eq_mul_right b_gt_0 rfl}

  rw [a_ex]
  simp_rw [euclid_gcd]
  exact r_n_gcd

  rename_i n induct
  --intro n
  --intro h
  rw [Nat.succ_eq_add_one]
  rw [combine_step]
  --rw [euc_gcd_ab_eq_gcd_ba]
  --apply gcd_ab_eq_gcd_ba

  have a_mod_sn_leq_n : (a % (n + 1)) ≤ n := by {exact Nat.lt_succ.mp (succ_mod_lt a n)}

  have r_gt_0_or_0 : (a % (n + 1) ≠ 0) ∨ (a % (n+1) = 0) := by {exact ne_or_eq (a % (n + 1)) 0}
  cases' r_gt_0_or_0 with r_neq_0 r_eq_0
  have r_gt_0 : a % (n + 1) > 0 := by {exact Nat.pos_of_ne_zero r_neq_0}
  --have a_gt_r : a > a % (n + 1) := by {have : a % (n+1) ≤ n+1 := by {exact Nat.le_step a_mod_sn_leq_n}; linarith}
  --have : _ := by {apply induct (a % (n+1)) (a_mod_sn_leq_n) (by assumption) (by assumption) (by assumption) (by assumption) }

  have : _ := by {apply induct (a % (n + 1)) (by assumption) (n+1) (by exact succ_mod_lt a n) (by exact r_gt_0) (by simp)}
  assumption

  {
    rw [r_eq_0]
    simp_rw [euclid_gcd]
    exact r_n_gcd
  }


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


#check euclid_alg_works 8 6 (by simp) (by simp)

def x : n_is_gcd 2 8 2 := ((n_is_gcd_iff_euclid _ _ _ (by simp) (by simp)).mpr) (rfl)
