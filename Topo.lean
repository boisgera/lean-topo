import Mathlib

import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

open unitInterval -- provides I

#check C(I, ℝ)

variable (A B : Set ℂ)

-- I don't like the standard mathlib IsPathConnected definition:
-- def IsPathConnected (F : Set X) : Prop :=
--   ∃ x ∈ F, ∀ {y}, y ∈ F → JoinedIn F x y
def IsPathConnected' (F : Set ℂ) : Prop :=
  ∀ x ∈ F, ∀ y ∈ F, JoinedIn F x y

theorem pc_union : IsPathConnected' A ∧ IsPathConnected' B ∧ (A ∩ B).Nonempty
  -> IsPathConnected' (A ∪ B)
  := by
  intro ⟨is_pc_A, is_pc_B, A_inter_B_non_empty⟩
  simp only [IsPathConnected'] at *
  simp only [Set.Nonempty] at A_inter_B_non_empty
  have ⟨z, z_in_A, z_in_B⟩ := A_inter_B_non_empty
  intro x x_in_A_or_B y y_in_A_or_B
  have A_sub_A_union_B : A ⊆ A ∪ B := Set.subset_union_left
  have B_sub_A_union_B : B ⊆ A ∪ B := Set.subset_union_right
  simp only [Set.mem_union] at x_in_A_or_B y_in_A_or_B
  cases x_in_A_or_B with
    | inl x_in_A =>
      cases y_in_A_or_B with
        | inl y_in_A =>
          have : JoinedIn A x y := is_pc_A x x_in_A y y_in_A
          exact JoinedIn.mono this A_sub_A_union_B
        | inr y_in_B =>
          have p1 : JoinedIn A x z := is_pc_A x x_in_A z z_in_A
          have p2 : JoinedIn B z y := is_pc_B z z_in_B y y_in_B
          exact JoinedIn.trans
            (JoinedIn.mono p1 A_sub_A_union_B)
            (JoinedIn.mono p2 B_sub_A_union_B)
    | inr x_in_B =>
      cases y_in_A_or_B with
        | inl y_in_A =>
          have p1 : JoinedIn B x z := is_pc_B x x_in_B z z_in_B
          have p2 : JoinedIn A z y := is_pc_A z z_in_A y y_in_A
          exact JoinedIn.trans
            (JoinedIn.mono p1 B_sub_A_union_B)
            (JoinedIn.mono p2 A_sub_A_union_B)
        | inr y_in_B =>
          have : JoinedIn B x y := is_pc_B x x_in_B y y_in_B
          exact JoinedIn.mono this B_sub_A_union_B

def separates (f : ℂ → ℝ) (A B : Set ℂ): Prop :=
  (∀ z ∈ A, f z < 0) ∧ (∀ z ∈ B, f z > 0)


#check intermediate_value_Icc
#check intermediate_value_univ₂

def zero_function (_ : I):= (0 : ℝ)

def zero_function_continuous : Continuous zero_function :=
  have isOpen_preimage: ∀ (O : Set ℝ), IsOpen O → IsOpen (zero_function⁻¹' O) := by
    intro O is_open_O
    let O' := zero_function⁻¹' O
    have two_cases: O' = ∅ ∨ O' = {0} := by
      match O.eq_empty_or_nonempty with
      | Or.inl o_empty =>
          apply Or.inl
          simp only [O', zero_function, o_empty, Set.preimage]
          simp only [Set.mem_empty_iff_false, Set.setOf_false]
      | Or.inr o_prime_non_empty =>
          apply Or.inr
          sorry -- TODO!
    sorry
  {isOpen_preimage := isOpen_preimage}


theorem PathDisconnected_of_continuous_separation :
  ∀ (f : ℂ → ℝ), (Continuous f) -> (separates f A B) -> A.Nonempty -> B.Nonempty
  -> ¬IsPathConnected' (A ∪ B) := by
  intro f f_cont f_separates_A_B A_nonempty B_nonempty
  intro is_path_connected_A_union_B
  have ⟨a, a_in_A⟩ := A_nonempty
  have ⟨b, b_in_B⟩ := B_nonempty
  simp [IsPathConnected'] at is_path_connected_A_union_B
  have a_in_A_or_B : a ∈ A ∪ B :=
    Set.subset_union_left a_in_A
  have b_in_A_or_B : b ∈ A ∪ B :=
    Set.subset_union_right b_in_B
  have j : JoinedIn (A ∪ B) a b :=
    is_path_connected_A_union_B a a_in_A_or_B b b_in_A_or_B
  simp only [JoinedIn] at j
  have ⟨γ, γ_in_A_or_B⟩ := j
  let ϕ := f ∘ γ
  have ϕ_cont := Continuous.comp f_cont γ.continuous
  have : intermediate_value_Icc (zero_le_one) ϕ_cont
  sorry
