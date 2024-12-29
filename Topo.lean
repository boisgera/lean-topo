import Mathlib

import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.UnitInterval

open unitInterval -- provides I

variable (A B : Set ℂ)

-- I don't like the standard mathlib IsPathConnected definition:
--     def IsPathConnected (F : Set X) : Prop :=
--     ∃ x ∈ F, ∀ {y}, y ∈ F → JoinedIn F x y
-- It is asymmetrical and entails that F.Nonempty (and y is implicit!).

def IsPathConnected' (F : Set ℂ) :=
  ∀ x ∈ F, ∀ y ∈ F, JoinedIn F x y

namespace Calculus

lemma is_unit_two : IsUnit (2 : ℝ) := IsUnit.mk0 2 (by norm_num)
lemma two_sub_one : (2 : ℝ) - 1 = 1 := by norm_num

-- Rk: we could also get rid of the first assumption here.
lemma lemma₁ (x : ℝ) (h₁ : 0 <= x) (h₂ : x ≤ 1/2) : 2 * x ≤ 1 := by
  have two_le_two : (2 : ℝ) ≤ 2 := le_refl 2
  have two_geq_zero : (2 : ℝ) ≥ 0 := zero_le_two
  have : 2 * x ≤ 2 * (1 / 2 : ℝ) := mul_le_mul two_le_two h₂ h₁ zero_le_two
  simp only [one_div] at this
  rw [IsUnit.mul_inv_cancel is_unit_two] at this
  assumption

lemma lemma₁' {x : ℝ} (h₁ : 0 <= x) (h₂ : x <= 1 / 2) : (2 * x ∈ I) := by
  constructor
  . linarith
  . linarith

lemma mul_le_mul' : ∀ {a b c : ℝ}, a ≤ b → 0 ≤ c → c * a <= c * b := by
  intro a b c a_le_b c_nonneg
  exact mul_le_mul_of_nonneg_left a_le_b c_nonneg

-- TODO: rewrite this with linarith more extensively?
lemma lemma₂ (x : ℝ) (h₁ : 1/2 <= x) (h₂ : x ≤ 1): 2 * x - 1 ∈ I := by
  rw [Set.mem_Icc]
  constructor
  . have h₃ : 2 * (1/2) <= 2 * x :=
      mul_le_mul (by norm_num) h₁ (by norm_num) (by norm_num)
    simp only [one_div] at h₃
    simp only [IsUnit.mul_inv_cancel is_unit_two] at h₃
    have h₄ : 1 - 1 <= 2 * x - 1:= sub_le_sub h₃ (by norm_num)
    simp only [sub_self] at h₄
    assumption
  . have : 2 * x <= 2 * 1 := mul_le_mul' h₂ (by norm_num)
    simp only [mul_one] at this
    have h : 2 * x - 1 <= 2 - 1 := sub_le_sub this (by norm_num)
    linarith
    -- simp only [two_sub_one] at this
    -- assumption

lemma lemma₂' {x : ℝ} (h₁ : 1/2 <= x) (h₂ : x ≤ 1) : 2 * x - 1 ∈ I := by
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
    -- TODO: define t' := (2 : ℝ) * ↑t, externalize the lemma that t'_in_I
    have zero_le_t : 0 <= ↑t := t.property.left
    have two_le_two : (2 : ℝ) ≤ 2 := le_refl 2
    have zero_le_two_t : 0 ≤ (2 : ℝ) * ↑t := mul_nonneg zero_le_two zero_le_t
    have two_t_le_one : (2 : ℝ) * ↑t ≤ 1 := Calculus.lemma₁ ↑t zero_le_t t_le_half
    rw [Path.extend_extends γ₁ (t := (2 : ℝ) * ↑t) ⟨zero_le_two_t, two_t_le_one⟩]
    apply γ₁_in_F
  | inr t_gt_half =>
    simp only [t_gt_half, reduceIte]
    let t' := (2 : ℝ) * ↑t - 1
    -- TODO: prove that 0 <= (2:ℝ) * ↑ t - 1 <= 1 (externally, that's cleaner)
    have t'_in_I : t' ∈ Set.Icc 0 1 :=
      sorry
    rw [Path.extend_extends γ₂ t'_in_I]
    apply γ₂_in_F

lemma IsPathConnected_iff {F : Set ℂ}:
  IsPathConnected F ↔ F.Nonempty ∧ IsPathConnected' F := by
  apply Iff.intro
  . intro is_pc
    have ⟨x, x_in_F, h⟩ := is_pc
    constructor
    . exact ⟨x, x_in_F⟩
    . intro y y_in_F z z_in_F
      simp only [JoinedIn]
      have ⟨γ₁, γ₁_in_F⟩ : JoinedIn F x y := h y_in_F
      have ⟨γ₂, γ₂_in_F⟩ : JoinedIn F x z := h z_in_F
      let γ := γ₁.symm.trans γ₂
      have γ_in_F :  ∀ (t : I), γ t ∈ F := by
        intro t
        simp only [γ, Path.trans]
        simp only [Path.coe_mk_mk, Function.comp_apply]
        cases (em (t <= (1 / 2 : ℝ))) with
        | inl t_le_half =>
          -- need to expand the implementation of γ₁.toFun
          simp only [t_le_half]
          simp only [reduceIte]
          have lem₁ : ∃ (t' : I), γ₁.symm.extend (2 * t) = γ₁ t' := by
            use (2 * t - 1) -- Nah, need the number, plus the proof that 0 <= z <= 1

            sorry
          have lem₂ : ∃ (t' : I), γ₂.extend (2 * t - 1) = γ₂ t' := by
            sorry

          sorry
        | inr t_gt_half =>
          -- need to expand the implementation of γ₂.toFun
          sorry




        -- cases (em (t <= (1 / 2 : ℝ))) with
        -- | inl t_le_half =>
        --   -- need to expand the implementation of γ.toFun
        --   sorry
        -- | inr t_gt_half =>
        --   sorry
        sorry
      sorry

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
