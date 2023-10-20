import linear_algebra.finite_dimensional

variables {K : Type} [field K]
variables {X : Type} [add_comm_group X] [module K X] [finite_dimensional K X]

open finite_dimensional submodule

lemma add_mem_of_mem_sub {K : Type*} [field K] {V : Type*} 
  [add_comm_group V] [module K V] {U : subspace K V} {v w : V} 
  (hv : v + w ∈ U) (hw : w ∈ U) : v ∈ U :=
begin
  have h : v = (v + w) - w,
  {  rw add_comm, rw add_sub_cancel' },
  rw h,
  exact U.sub_mem hv hw,
end


theorem my_thm --  W ⊂ U → U ∩ (V + W) = U ∩ V + W
( U V W : subspace K X )  
( W : subspace K U )
:
U ⊓ (V + W.map U.subtype) = U ⊓ V + W.map U.subtype
:= 

-- Proof that the LHS is a subset of the RHS
begin
  rw le_antisymm_iff,
  split,
  {
    intro z,
    intro h1,
    cases h1,
    -- Unpack the membership of x in V + W
    rcases mem_sup.1 h1_right with ⟨v, hvV, w, hwW, rfl⟩,
    --rw add_comm,


    -- Express w in terms of an element of W
    rcases mem_map.1 hwW with ⟨w', hw'W, rfl⟩,

    have j : (v ∈ U ⊓ V),
    begin
    rw mem_inf,
    split,
    {exact add_mem_of_mem_sub h1_left w'.2,
    },
    {apply hvV,},
    end,

    have k : (v ∈ U ⊓ V + map (submodule.subtype U) W),
    begin
    exact mem_sup_left j,
    end,

    have l : ((submodule.subtype U) w' ∈ U ⊓ V + map (submodule.subtype U) W),
    begin
    apply mem_sup_right,
    exact hwW,
    end,
    -- Since v is in U ⊓ V and w' is in W (mapped to U), their sum is in U ⊓ V + W
    apply add_mem k l,
  },
  { 
    
    intro z,
    intro h2,
    rcases mem_sup.1 h2 with ⟨uv, hUV, w, hwW, rfl⟩,

    have j : (uv ∈ U),
    begin
    exact (mem_inf.1 hUV).1
    end,

    have o : (w ∈ U),
    begin
    -- Step 1: Obtain the pre-image of w under the subtype inclusion.
    rcases hwW with ⟨w', hw'W, hw_eq⟩,
    rwa ← hw_eq,
    exact w'.property,
    end,

    split,
    apply add_mem j o,

    have h_uv_in_sum : (uv ∈ ↑(V + map (submodule.subtype U) W)),
    { 
      exact mem_sup_left (mem_inf.1 hUV).right,
    },

    have h_w_in_sum : (w ∈ ↑(V + map (submodule.subtype U) W)),
    {
      exact mem_sup_right hwW,
    },

    exact (V + map (submodule.subtype U) W).add_mem h_uv_in_sum h_w_in_sum 
    -- need to apply add_mem in the context of V+map
}
end
