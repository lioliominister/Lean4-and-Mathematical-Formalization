import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Topology.Defs.Basic
import Mathlib.Data.Set.Basic

set_option linter.deprecated.module false

variable {H : Type*} [NormedAddCommGroup H] [CompleteSpace H] [InnerProductSpace ℝ H]

def is_convex (E : Set H) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, ∀(k : ℝ), 0 ≤ k → k ≤ 1 → x + (k : ℝ) • (y - x) ∈ E

variable {C : Set H} (conv_c : is_convex C) (close_c : IsClosed C) (nonempty_c : Set.Nonempty C)
variable (x y : H)

def is_nearest_point (x y : H) := y ∈ C ∧ ∀ z ∈ C, ‖z - x‖^2 ≥ ‖y - x‖^2
def is_proj (x y : H) := @is_nearest_point _ _ C x y

theorem projection_iff_vi (x y : H)
  :  @is_proj _ _ C x y ↔ y ∈ C ∧ ∀ z ∈ C, inner ℝ (x - y) (z - y) ≤ 0
  := by
    unfold is_proj
    unfold is_nearest_point
    constructor
    · rintro ⟨yc, h⟩
      constructor
      · exact yc
      · intro z zc
        have proj_ineq : ‖z - x‖ ^ 2 ≥ ‖y - x‖ ^ 2 := h z zc
        rw [<- add_zero z, <- sub_self y, add_sub, add_sub_right_comm, <- add_sub, @norm_add_pow_two ℝ _ _ _ _ (z - y) (y - x)] at proj_ineq
        sorry
    · rintro zc_inn_le_zero
      constructor
      · exact zc_inn_le_zero.1
      · intro z zc
        rw [<- add_zero z, <- sub_self y, add_sub, add_sub_right_comm, <- add_sub, @norm_add_pow_two ℝ _ _ _ _ (z - y) (y - x), add_comm]
        nth_rw 2 [<- add_zero (‖y - x‖ ^ 2)]
        -- simp
        apply (add_le_add_iff_left (‖y - x‖ ^ 2)).2
        rw [real_inner_comm]
        have inner_nonneg : inner ℝ (y - x) (z - y) ≥ 0 := by
          have : inner ℝ (x - y) (z - y) ≤ 0 := zc_inn_le_zero.2 z zc
          rw [<- neg_sub x y, inner_neg_left]
          simpa
        have norm_pow_two_nonneg : ‖z - y‖ ^ 2 ≥ 0 := by
          apply pow_two_nonneg
        simp [add_nonneg, inner_nonneg, norm_pow_two_nonneg]

lemma abel_trans {a b c : H} : a - b + c = c - b + a := by abel

theorem firmly_non_expansive
  (x x' y y' : H) (hx : @is_proj _ _ C x x') (hy : @is_proj _ _ C y y')
  (x'c : x' ∈ C) (y'c : y' ∈ C) (xney : x ≠ y) (x'ney': x' ≠ y')
  :  inner ℝ (x' - y') (x - y) ≥ ‖x' - y'‖^2
  := by
    unfold is_proj at hx
    unfold is_proj at hy
    unfold is_nearest_point at hx
    unfold is_nearest_point at hy
    have hx_inner : ∀ z ∈ C, inner ℝ (x - x') (z - x') ≤ 0 := by
      exact ((projection_iff_vi x x').1 hx).2
    have hy_inner : ∀ z ∈ C, inner ℝ (y - y') (z - y') ≤ 0 := by
      exact ((projection_iff_vi y y').1 hy).2
    have inner_mul_inner_le_zero
      :  inner ℝ (x - x') (y' - x') + inner ℝ (y - y') (x' - y') ≤ 0
      := by
        have this₁ : inner ℝ (x - x') (y' - x') ≤ 0 := hx_inner y' y'c
        have this₂ : inner ℝ (y - y') (x' - y') ≤ 0 := hy_inner x' x'c
        apply add_nonpos this₁ this₂
    rw [<- neg_sub x' x, <- neg_sub x' y'] at inner_mul_inner_le_zero
    rw [inner_neg_left, inner_neg_right, neg_neg] at inner_mul_inner_le_zero
    rw [<- inner_add_left, add_sub, abel_trans, <- add_sub] at inner_mul_inner_le_zero
    rw [inner_add_left] at inner_mul_inner_le_zero
    rw [<- neg_sub, inner_neg_left, real_inner_comm, neg_add_eq_sub, sub_le_iff_le_add, zero_add] at inner_mul_inner_le_zero
    rw [<- @inner_self_eq_norm_sq ℝ H _ _ _ (x' - y')]
    exact inner_mul_inner_le_zero

theorem non_expansive
  (x x' y y' : H) (hx : @is_proj _ _ C x x') (hy : @is_proj _ _ C y y')
  (x'c : x' ∈ C) (y'c : y' ∈ C) (xney : x ≠ y) (x'ney': x' ≠ y')
  :  ‖x' - y'‖ ≤ ‖x - y‖
  := by
    have use_firmly_non_expansive
      : inner ℝ (x' - y') (x - y) ≥ ‖x' - y'‖^2
      := firmly_non_expansive x x' y y' hx hy x'c y'c xney x'ney'
    unfold is_proj at hx
    unfold is_proj at hy
    unfold is_nearest_point at hx
    unfold is_nearest_point at hy
    have inner_le_norm_mul_norm
      : inner ℝ (x' - y') (x - y) ≤ ‖x' - y'‖ * ‖x - y‖
      := by apply real_inner_le_norm (x' - y') (x - y)
    -- have xney₁ : x - y ≠ 0 := by
    --   rw [sub_ne_zero]
    --   exact xney
    have x'ney'₁ : x' - y' ≠ 0 := by
      rw [sub_ne_zero]
      exact x'ney'
    have norm_x'suby'_pos : ‖x' - y'‖ > 0 := by
      apply (@norm_pos_iff H _ (x' - y')).2
      exact x'ney'₁
    have : ‖x' - y'‖ ^ 2 ≤ ‖x' - y'‖ * ‖x - y‖ := by
      exact le_trans use_firmly_non_expansive inner_le_norm_mul_norm
    rw [pow_two ‖x' - y'‖] at this
    apply (mul_le_mul_iff_of_pos_left norm_x'suby'_pos).1 at this
    exact this
