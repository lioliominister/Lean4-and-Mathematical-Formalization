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
  :  @is_proj _ _ C x y ↔ ∀ z ∈ C, inner ℝ (x - y) (z - y) ≤ 0
  := by
    unfold is_proj
    unfold is_nearest_point
    constructor
    · rintro ⟨yc, h⟩
      intro z zc
      have proj_ineq : ‖z - x‖ ^ 2 ≥ ‖y - x‖ ^ 2 := h z zc
      rw [<- add_zero z, <- sub_self y, add_sub, add_sub_right_comm, <- add_sub, @norm_add_pow_two ℝ _ _ _ _ (z - y) (y - x)] at proj_ineq
      sorry
    · rintro zc_inn_le_zero
      constructor
      ·
        sorry
      · intro z zc
        rw [<- add_zero z, <- sub_self y, add_sub, add_sub_right_comm, <- add_sub, @norm_add_pow_two ℝ _ _ _ _ (z - y) (y - x)]
        have is_pow_two_nonneg : ‖z - y‖ ^ 2 := by sorry
        sorry
