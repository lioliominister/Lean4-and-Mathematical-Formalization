import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Data.Set.Basic

set_option linter.deprecated.module false

variable {H : Type*} [NormedAddCommGroup H] [CompleteSpace H] [InnerProductSpace ℝ H]
variable {C : Set H} (conv_c : Convex ℝ C) (close_c : IsClosed C) (nonempty_c : Set.Nonempty C)

variable (x y : H)

def proj (C : Set H) (x x' : H) := ‖x - x'‖ = ⨅ (w : ↑C), ‖x - ↑w‖

#check exists_norm_eq_iInf_of_complete_convex
#check norm_eq_iInf_iff_real_inner_le_zero

lemma abel_trans {a b c : H} : a - b + c = c - b + a := by abel

lemma proj_exists (C : Set H) (conv_c : Convex ℝ C) (close_c : IsClosed C) (nonempty_c : C.Nonempty) (x : H) : ∃ x' : H, x' ∈ C ∧ proj C x x' := by
  have complete_c : IsComplete C := by
    apply IsClosed.isComplete close_c
  rcases exists_norm_eq_iInf_of_complete_convex nonempty_c complete_c conv_c x with ⟨p, ⟨pc, hp⟩⟩
  use p
  exact ⟨pc, hp⟩

theorem non_expansive (x x' y y' : H) (conv_c : Convex ℝ C) (x'c : x' ∈ C) (y'c : y' ∈ C) (x_proj_x' : proj C x x') (y_proj_y' : proj C y y')
  :  ‖x' - y'‖ ≤ ‖x - y‖
  := by
    have vi_x_x' : ∀ w ∈ C, inner ℝ (x - x') (w - x') ≤ 0 := by
      apply (norm_eq_iInf_iff_real_inner_le_zero conv_c x'c).1 x_proj_x'
    have vi_y_y' : ∀ w ∈ C, inner ℝ (y - y') (w - y') ≤ 0 := by
      apply (norm_eq_iInf_iff_real_inner_le_zero conv_c y'c).1 y_proj_y'
    have vi_x_x'_y' : inner ℝ (x - x') (y' - x') ≤ 0 := vi_x_x' y' y'c
    have vi_y_y'_x' : inner ℝ (y - y') (x' - y') ≤ 0 := vi_y_y' x' x'c
    have vi_add : inner ℝ (y - x + x' - y') (x' - y') ≤ 0 := by
      rw [<- neg_sub x' y', <- neg_sub x' x, inner_neg_left, inner_neg_right, neg_neg] at vi_x_x'_y'
      have : inner ℝ (x' - x + y - y') (x' - y') ≤ 0 := by
        rw [<- add_sub, inner_add_left (x' - x) (y - y') (x' - y')]
        apply add_nonpos vi_x_x'_y' vi_y_y'_x'
      rw [abel_trans]
      exact this
    rw [<- add_sub, inner_add_left, <- neg_sub x y, inner_neg_left] at vi_add
    have inner_le_inner : inner ℝ (x' - y') (x' - y') ≤ inner ℝ (x - y) (x' - y') := by
      linarith
    have norm_mul_norm_le_norm_mul_norm : ‖x' - y'‖^2 ≤ ‖x - y‖ * ‖x' - y'‖ := by
      rw [<- @inner_self_eq_norm_sq ℝ _ _ _ _ (x' - y'), RCLike.re_to_real]
      calc
        inner ℝ (x' - y') (x' - y') ≤ inner ℝ (x - y) (x' - y') := by
          exact inner_le_inner
        _ ≤ _ := by
          apply real_inner_le_norm
    rw [sq] at norm_mul_norm_le_norm_mul_norm
    have norm_nonneg₁ : ‖x' - y'‖ ≥ 0 := by
      apply norm_nonneg
    rcases norm_nonneg₁.eq_or_lt with norm_zero | norm_pos
    · rw [<- norm_zero]
      apply norm_nonneg
    · apply (mul_le_mul_iff_of_pos_right norm_pos).1
      exact norm_mul_norm_le_norm_mul_norm


-- ∀ w ∈ C, inner ℝ (x - x') (w - x') ≤ 0
-- w : H → w ∈ C → inner ℝ (x - x') (w - x') ≤ 0
