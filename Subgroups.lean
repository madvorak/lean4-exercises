import Mathlib.GroupTheory.Subgroup.Basic


def IsA (S : Type) {α : Type} [SetLike S α] (s : Set α) : Prop :=
  ∃ (m : S), (m : Set α) = s

theorem comparable_of_union_subgroups {G : Type} [Group G]
    (H₁ H₂ : Subgroup G) (hyp : IsA (Subgroup G) (H₁ ∪ H₂)) :
  H₁ ≤ H₂  ∨  H₂ ≤ H₁  :=
by
  by_contra contr
  push_neg at contr
  obtain ⟨a, a_in, a_ni⟩ : ∃ a ∈ H₁, a ∉ H₂
  · exact Iff.mp Set.not_subset contr.1
  obtain ⟨b, b_in, b_ni⟩ : ∃ b ∈ H₂, b ∉ H₁
  · exact Iff.mp Set.not_subset contr.2
  clear contr

  rcases hyp with ⟨H, hyp'⟩
  have hyp := Set.ext_iff.mp hyp'
  clear hyp'
  simp only [SetLike.mem_coe] at hyp
  
  have a_in_union : a ∈ (H₁ ∪ H₂ : Set G)
  · exact Set.mem_union_left (↑H₂) a_in
  have b_in_union : b ∈ (H₁ ∪ H₂ : Set G)
  · exact Set.mem_union_right (↑H₁) b_in
  have ab_in_union : a * b ∈ (H₁ ∪ H₂ : Set G)
  · rw [← hyp] at a_in_union b_in_union ⊢
    exact Subgroup.mul_mem H a_in_union b_in_union
  rw [Set.mem_union] at ab_in_union
  cases' ab_in_union with inH₁ inH₂
  · have aab_in : a⁻¹ * (a * b) ∈ ↑H₁
    · have a_inv : a⁻¹ ∈ ↑H₁
      · exact Subgroup.inv_mem H₁ a_in
      exact Subgroup.mul_mem H₁ a_inv inH₁
    rw [← mul_assoc, mul_left_inv, one_mul] at aab_in
    exact b_ni aab_in
  · have abb_in : (a * b) * b⁻¹ ∈ ↑H₂
    · have b_inv : b⁻¹ ∈ ↑H₂
      · exact Subgroup.inv_mem H₂ b_in
      exact Subgroup.mul_mem H₂ inH₂ b_inv
    rw [mul_assoc, mul_right_inv, mul_one] at abb_in
    exact a_ni abb_in
