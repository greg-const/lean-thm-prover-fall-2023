import Mathlib.LinearAlgebra.FiniteDimensional

variable (K : Type u) [Field K]
variable (X : Type v) [AddCommGroup X] [Module K X] [FiniteDimensional K X]

open FiniteDimensional Submodule

lemma add_mem_of_mem_sub {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V] {U : Subspace K V} {v w : V} (hv : v + w ∈ U) (hw : w ∈ U) : v ∈ U := by
{
  have h : v = (v + w) - w := by
  { rw [add_comm, add_sub_cancel']}
  rw [h]
  exact U.sub_mem hv hw
}

theorem my_thm
( U V : Subspace K X)
( W : Subspace K U)
:
U ⊓ (V + W.map U.subtype) = U ⊓ V + W.map U.subtype := by
{
  rw [le_antisymm_iff]
  apply And.intro -- had to use this instead of split
  {
    intro z
    intros h1
    rw [mem_inf] at h1 -- had to use this instead of cases. trying to figure out why
    have h1_left : z ∈ U := by {exact h1.left}
    have h1_right : z ∈ V + map (Submodule.subtype U) W := by {exact h1.right}

    rcases mem_sup.1 h1_right with ⟨v, hvV, w, hwW, rfl⟩
    rcases mem_map.1 hwW with ⟨w', _, rfl⟩

    have v_in_U_int_V : v ∈ U ⊓ V := by
      {rw [mem_inf]
       apply And.intro
       exact add_mem_of_mem_sub h1_left w'.2
       exact hvV}

    have v_in_RHS : (v ∈ U ⊓ V + map (Submodule.subtype U) W) := by {exact mem_sup_left v_in_U_int_V}

    have w_in_RHS : (Submodule.subtype U) w' ∈ U ⊓ V + map (Submodule.subtype U) W := by {apply mem_sup_right; exact hwW}

    apply add_mem v_in_RHS w_in_RHS

  }
  {
    intro z
    intro h2
    rcases mem_sup.1 h2 with ⟨uv, hUV, w, hwW, rfl⟩
    have uv_in_U : (uv ∈ U) := by { exact (mem_inf.1 hUV).1 }

    have w_in_U : (w ∈ U) := by
    {
      rcases hwW with ⟨w', _, hw_eq⟩
      rw [← hw_eq]
      exact w'.property
    }

    rw [mem_inf]
    apply And.intro
    {apply add_mem uv_in_U w_in_U}
    {
      have uv_in_sum : (uv ∈ ↑(V + map (Submodule.subtype U) W)) := by {exact mem_sup_left (mem_inf.1 hUV).right}

      have w_in_sum : (w ∈ ↑(V + map (Submodule.subtype U) W)) := by {exact mem_sup_right hwW}

      exact (V + map (Submodule.subtype U) W).add_mem uv_in_sum w_in_sum
    }
  }
}
