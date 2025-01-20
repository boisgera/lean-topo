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
def IsPathConnected' (F : Set ℂ) := ∀ x ∈ F, ∀ y ∈ F, JoinedIn F x y

namespace Calculus

lemma lemma₁ {x : ℝ} (h₁ : 0 <= x) (h₂ : x <= 1 / 2) : 2 * x ∈ I := by
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

def IsConnected' (F : Set ℂ) := IsPreconnected F

lemma not_empty_iff_nonempty {F : Set ℂ} : F.Nonempty ↔ ¬F = ∅ := by
  constructor
  . intro F_nonempty
    intro F_empty
    have ⟨x, x_in_F⟩ := F_nonempty
    rw [F_empty] at x_in_F
    exact x_in_F
  . intro F_not_empty
    by_contra F_empty
    push_neg at F_empty
    exact F_not_empty F_empty


theorem connected_of_path_connected (F : Set ℂ) : IsPathConnected' F → IsConnected' F := by
  intro is_path_connected
  rw [IsConnected', IsPreconnected]
  intro u v is_open_u is_open_v F_sub_u_v F_inter_v_non_empty F_inter_u_non_empty
  -- We introduce a path γ that joins a ∈ u and b ∈ v in u ∪ v ;
  -- use it to get γ.extend u' and γ.extend v' open sets of ℝ and leverage the
  -- fact that ℝ is preconnected to deduce that γ.extend u' ∩ γ.extend v' ≠ ∅ ;
  -- that provides a contradiction since γ.extend u' ∩ γ.extend v' = γ.extend (u ∩ v)
  have ⟨a, a_in_F_and_u⟩ := F_inter_u_non_empty
  have ⟨b, b_in_F_and_v⟩ := F_inter_v_non_empty
  have ⟨γ, γ_in_F⟩ := is_path_connected a a_in_F_and_u.left b b_in_F_and_v.left
  have γ_extend_cont := γ.continuous_extend

  have is_connected_ℝ : IsPreconnected (Set.univ : Set ℝ) := by
    sorry
  rw [IsPreconnected] at is_connected_ℝ
  simp only [Set.univ_inter] at is_connected_ℝ

  have is_open_u' := is_open_u.preimage γ_extend_cont
  have is_open_v' := is_open_v.preimage γ_extend_cont
  set u' := γ.extend⁻¹' u with u'_def
  set v' := γ.extend⁻¹' v with v'_def
  have h₁ : Set.univ ⊆ u' ∪ v' := sorry
  have h₂ : u'.Nonempty := sorry
  have h₃ : v'.Nonempty := sorry
  have h₄ := is_connected_ℝ u' v' is_open_u' is_open_v' h₁ h₂ h₃

  rw [u'_def, v'_def] at h₄
  rw [<-Set.preimage_inter] at h₄
  -- at this stage, we only need to go from h₄ : (γ.extend ⁻¹' (u ∩ v)).Nonempty
  -- to ⊢ (F ∩ (u ∩ v)).Nonempty
  sorry

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
    have O'_def : O' = zero_function⁻¹' O := by rfl
    rw [<-O'_def]
    cases (em (O'.Nonempty)) with
    | inl O'_non_empty =>
      have ⟨t, zero_in_O'⟩ := O'_non_empty
      have O_prime_eq_univ: O' = Set.univ := by
        let ⟨x₀, x₀_in_O'⟩ := O'_non_empty
        simp only [O'] at x₀_in_O'
        simp only [zero_function, Set.mem_preimage] at x₀_in_O'
        simp only [O']
        ext x
        simp only [Set.mem_preimage, Set.mem_univ, iff_true]
        rw [zero_function]
        assumption
      have := isOpen_univ (X := Set I)
      rw [O_prime_eq_univ]
      exact isOpen_univ
    | inr O'_empty =>
      push_neg at O'_empty
      have := empty_set_is_open
      rw [O'_empty]
      assumption
  {isOpen_preimage := isOpen_preimage}

def separates (f : ℂ → ℝ) (A B : Set ℂ): Prop :=
  (∀ z ∈ A, f z < 0) ∧ (∀ z ∈ B, f z > 0)

theorem path_disconnected_of_continuous_separation:
  ∀ (f : ℂ → ℝ), (Continuous f) -> (separates f A B) -> A.Nonempty -> B.Nonempty
  -> ¬IsPathConnected' (A ∪ B) := by
  intro f f_cont f_separates_A_B A_nonempty B_nonempty
  have ⟨f_A_neg, f_B_pos⟩ := f_separates_A_B
  intro is_path_connected_A_union_B
  have ⟨a, a_in_A⟩ := A_nonempty
  have ⟨b, b_in_B⟩ := B_nonempty
  simp [IsPathConnected'] at is_path_connected_A_union_B
  have a_in_A_or_B : a ∈ A ∪ B :=
    Set.subset_union_left a_in_A
  have b_in_A_or_B : b ∈ A ∪ B :=
    Set.subset_union_right b_in_B
  have ⟨γ, γ_in_A_or_B⟩ : JoinedIn (A ∪ B) a b :=
    is_path_connected_A_union_B a a_in_A_or_B b b_in_A_or_B
  set ϕ := f ∘ γ.extend with ϕ_def
  have ϕ_cont := Continuous.comp f_cont γ.continuous_extend
  have iv : Set.Icc (ϕ 0) (ϕ 1) ⊆ ϕ '' Set.Icc 0 1 :=
    intermediate_value_Icc (zero_le_one) (Continuous.continuousOn (s := I) ϕ_cont)
  have begin_neg: ϕ 0 < 0 := by
    rw [ϕ_def, Function.comp]
    apply f_A_neg
    simp only [
      Set.mem_Icc,
      le_refl,
      zero_le_one,
      and_self,
      Path.extend_extends,
      Set.Icc.mk_zero,
      Path.source
    ]
    assumption
  have end_pos: ϕ 1 > 0 := by
    rw [ϕ_def, Function.comp]
    apply f_B_pos
    simp only [
      Set.mem_Icc,
      zero_le_one,
      le_refl,
      and_self,
      Path.extend_extends,
      Set.Icc.mk_one,
      Path.target
    ]
    assumption
  have zero_in_range : 0 ∈ Set.Icc (ϕ 0) (ϕ 1) := by
    simp only [Set.mem_Icc]
    constructor
    . exact (le_of_lt begin_neg)
    . exact (le_of_lt end_pos)
  have zero_in_image_ϕ : 0 ∈ ϕ '' Set.Icc 0 1 := iv zero_in_range
  have ⟨t, t_in_I, ϕ_t_eq_0⟩ := zero_in_image_ϕ
  have γ_in_A_or_B_t := γ_in_A_or_B ⟨t, t_in_I⟩
  have ϕ_t_neg_or_pos : (ϕ t < 0) ∨ (ϕ t > 0) := by
    cases γ_in_A_or_B_t with
    | inl γ_in_A_t => -- γ ⟨t, t_in_I⟩ ∈ A; prove ϕ t < 0
        apply Or.inl
        rw [ϕ_def]
        apply f_A_neg
        rw [Path.extend_extends]
        assumption
    | inr γ_in_B_t =>  -- γ ⟨t, t_in_I⟩ ∈ B; prove ϕ t > 0
        apply Or.inr
        rw [ϕ_def]
        apply f_B_pos
        rw [Path.extend_extends]
        assumption
  cases ϕ_t_neg_or_pos with
  | inl ϕ_t_neg => rw [ϕ_t_eq_0] at ϕ_t_neg; linarith
  | inr ϕ_t_pos => rw [ϕ_t_eq_0] at ϕ_t_pos; linarith
