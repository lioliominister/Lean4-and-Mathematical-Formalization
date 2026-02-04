import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic


open RealInnerProductSpace


variable {E : Type*} [InnerProductSpace ℝ E] [CompleteSpace E]

variable {C : Set E} (hC_closed : IsClosed C) (hC_conv : Convex ℝ C) (hC_nonempty : C.Nonempty)


local notation "P" => orthogonalProjection hC_closed hC_conv hC_nonempty

theorem projection_is_1_lipschitz (x1 x2 : E) : ‖P x1 - P x2‖ ≤ ‖x1 - x2‖ := by
  let p1 := P x1
  let p2 := P x2


  have h_vi1 : ⟪x1 - p1, p2 - p1⟫ ≤ 0 :=
    inner_orthogonalProjection_left_le_zero hC_closed hC_conv hC_nonempty x1 p2


  have h_vi2 : ⟪x2 - p2, p1 - p2⟫ ≤ 0 :=
    inner_orthogonalProjection_left_le_zero hC_closed hC_conv hC_nonempty x2 p1


  have h_fne : ‖p1 - p2‖^2 ≤ ⟪x1 - x2, p1 - p2⟫ := by

    have h_sum : ⟪p1 - x1 + (x2 - p2), p1 - p2⟫ ≤ 0 := by
      rw [inner_add_left]
      linarith [h_vi1, h_vi2]


    calc ‖p1 - p2‖^2
      _ = ⟪p1 - p2, p1 - p2⟫ := by rw [pow_two, inner_self_eq_norm_sq]
      _ = ⟪(x1 - x2) + (p1 - p2 - (x1 - x2)), p1 - p2⟫ := by simp
      _ = ⟪x1 - x2, p1 - p2⟫ + ⟪(p1 - p2) - (x1 - x2), p1 - p2⟫ := by rw [inner_add_left]; simp
      _ ≤ ⟪x1 - x2, p1 - p2⟫ + 0 := add_le_add_left (by
          simp [sub_eq_add_neg] at h_sum ⊢
          exact h_sum
        ) _
      _ = ⟪x1 - x2, p1 - p2⟫ := add_zero _


  have h_cs : ⟪x1 - x2, p1 - p2⟫ ≤ ‖x1 - x2‖ * ‖p1 - p2‖ := real_inner_le_norm _ _

  have h_final : ‖p1 - p2‖^2 ≤ ‖x1 - x2‖ * ‖p1 - p2‖ := h_fne.trans h_cs

  exact (pow_two_le_mul_self_iff ‖p1 - p2‖ ‖x1 - x2‖).mp h_final
