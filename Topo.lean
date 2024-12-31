import Mathlib

import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

open unitInterval -- provides I

variable (A B : Set ℂ)

-- The standard mathlib IsPathConnected definition:
--
--     def IsPathConnected (F : Set X) : Prop :=
--     ∃ x ∈ F, ∀ {y}, y ∈ F → JoinedIn F x y
--
-- is asymmetrical, entails that F.Nonempty and y is implicit.
--
-- A more classical definition would be:
def IsPathConnected' (F : Set ℂ) :=
  ∀ x ∈ F, ∀ y ∈ F, JoinedIn F x y

namespace Calculus

lemma lemma₁ {x : ℝ} (h₁ : 0 <= x) (h₂ : x <= 1 / 2) : (2 * x ∈ I) := by
  constructor
  . linarith
  . linarith

lemma lemma₂ {x : ℝ} (h₁ : 1/2 <= x) (h₂ : x ≤ 1) : 2 * x - 1 ∈ I := by
  constructor
  . linarith
  . linarith

end Calculus

lemma PathConcatenation {F : Set ℂ} {x y z : ℂ} :
  JoinedIn F x y → JoinedIn F y z → JoinedIn F x z := by
  intro j₁ j₂
  have ⟨γ₁, γ₁_in_F⟩ := j₁
  have ⟨γ₂, γ₂_in_F⟩ := j₂
  rw [JoinedIn]
  let γ := γ₁.trans γ₂
  use γ
  intro t
  simp only [γ, Path.trans, Path.coe_mk_mk, Function.comp_apply]
  cases (em (t ≤ (1 / 2 : ℝ))) with
  | inl t_le_half =>
    simp only [t_le_half, reduceIte]
    have zero_le_t : 0 <= ↑t := t.property.left
    have two_le_two : (2 : ℝ) ≤ 2 := le_refl 2
    have zero_le_two_t : 0 ≤ (2 : ℝ) * ↑t := mul_nonneg zero_le_two zero_le_t
    have : (2 : ℝ) * ↑t ∈ I := Calculus.lemma₁ zero_le_t t_le_half
    rw [Path.extend_extends γ₁ (t := (2 : ℝ) * ↑t) this]
    apply γ₁_in_F
  | inr t_gt_half =>
    simp only [t_gt_half, reduceIte]
    let t' := (2 : ℝ) * ↑t - 1
    have : (1/2 : ℝ) <= t := by
      simp only [not_le] at t_gt_half
      exact le_of_lt t_gt_half
    have t'_in_I : t' ∈ Set.Icc 0 1 :=
      Calculus.lemma₂ this t.property.right
    rw [Path.extend_extends γ₂ t'_in_I]
    apply γ₂_in_F

theorem IsPathConnected_iff {F : Set ℂ}:
  IsPathConnected F ↔ F.Nonempty ∧ IsPathConnected' F := by
  apply Iff.intro
  . intro is_pc
    have ⟨x, x_in_F, h⟩ := is_pc
    constructor
    . exact ⟨x, x_in_F⟩
    . intro y y_in_F z z_in_F
      have h₁ : JoinedIn F x y := h y_in_F
      have h₂ : JoinedIn F x z := h z_in_F
      exact PathConcatenation h₁.symm h₂
  . intro ⟨⟨x, x_in_F⟩, h⟩
    use x
    constructor
    . assumption
    . exact fun y_in_F => h x x_in_F _ y_in_F

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

def zero_function (_ : I) := (0 : ℝ)

lemma empty_set_is_open : IsOpen (∅ : Set I) := by
  have empty_eq_union_empty : ∅ = (⋃₀ ∅ : Set I) := by
    simp only [Set.sUnion_empty]
  have h : ∀ t ∈ (∅: Set (Set I)), IsOpen t := by
    intro t t_in_empty
    exfalso
    exact Set.not_mem_empty t t_in_empty
  have := isOpen_sUnion h
  simp only [Set.sUnion_empty] at this
  assumption

def zero_function_continuous : Continuous zero_function :=
  have isOpen_preimage: ∀ (O : Set ℝ), IsOpen O → IsOpen (zero_function⁻¹' O) := by
    intro O is_open_O
    let O' := zero_function⁻¹' O
    cases (em (O'.Nonempty)) with
    | inl O'_non_empty =>
      have ⟨t, zero_in_O'⟩ := O'_non_empty
      have : zero_function⁻¹' {0} = Set.univ := by
        simp_all
        intro x y
        simp only [zero_function, Set.mem_preimage, Set.mem_singleton_iff]
        intro _
        exact Eq.symm
      -- TODO: missing stuff here : O' is the full space, thus open.
      sorry
    | inr O'_empty =>
      push_neg at O'_empty
      have := empty_set_is_open
      simp only [O'] at O'_empty
      rw [O'_empty]
      assumption
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
  let ϕ := f ∘ γ.extend
  have ϕ_cont := Continuous.comp f_cont γ.continuous_extend
  have iv := intermediate_value_Icc (zero_le_one) (Continuous.continuousOn (s := Set.Icc 0 1) ϕ_cont)
  -- Set.Icc ((f ∘ γ.extend) 0) ((f ∘ γ.extend) 1) ⊆ f ∘ γ.extend '' Set.Icc 0 1
  -- TODO: \exists t ∈ Set.Icc 0 1, (f ∘ γ.extend) t = 0
  -- TODO: exhibit the contradiction (γ is a path of A ∪ B and f separates A and B)
  sorry
