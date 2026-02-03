import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic

/-!
# 投影算子的 1-Lipschitz 连续性证明
证明在实内积空间中，向闭凸集的投影算子是收缩映射（Contractive Map）。
-/

open RealInnerProductSpace

-- 定义变量：E 是一个完备的实内积空间（希尔伯特空间）
variable {E : Type*} [InnerProductSpace ℝ E] [CompleteSpace E]
-- 定义 C 是一个闭且凸的非空集合
variable {C : Set E} (hC_closed : IsClosed C) (hC_conv : Convex ℝ C) (hC_nonempty : C.Nonempty)

-- 定义投影算子的简写 P
local notation "P" => orthogonalProjection hC_closed hC_conv hC_nonempty

/--
定理：对于空间中的任意两点 x1 和 x2，其投影点之间的距离不大于原点之间的距离。
即：‖P x1 - P x2‖ ≤ ‖x1 - x2‖
-/
theorem projection_is_1_lipschitz (x1 x2 : E) : ‖P x1 - P x2‖ ≤ ‖x1 - x2‖ := by
  let p1 := P x1
  let p2 := P x2

  -- 关键引理 1：利用投影算子的变分不等式性
  -- 对于投影点 p1，任意点 y ∈ C，都有 ⟪x1 - p1, y - p1⟫ ≤ 0
  have h_vi1 : ⟪x1 - p1, p2 - p1⟫ ≤ 0 :=
    inner_orthogonalProjection_left_le_zero hC_closed hC_conv hC_nonempty x1 p2

  -- 关键引理 2：同理对于 p2
  have h_vi2 : ⟪x2 - p2, p1 - p2⟫ ≤ 0 :=
    inner_orthogonalProjection_left_le_zero hC_closed hC_conv hC_nonempty x2 p1

  -- 核心代数推导：证明 ‖p1 - p2‖² ≤ ⟪x1 - x2, p1 - p2⟫
  have h_fne : ‖p1 - p2‖^2 ≤ ⟪x1 - x2, p1 - p2⟫ := by
    -- 将两个不等式相加
    have h_sum : ⟪p1 - x1 + (x2 - p2), p1 - p2⟫ ≤ 0 := by
      rw [inner_add_left]
      -- 使用 linarith 处理实数不等式
      linarith [h_vi1, h_vi2]

    -- 展开内积并进行比较
    calc ‖p1 - p2‖^2
      _ = ⟪p1 - p2, p1 - p2⟫ := by rw [pow_two, inner_self_eq_norm_sq]
      _ = ⟪(x1 - x2) + (p1 - p2 - (x1 - x2)), p1 - p2⟫ := by simp
      _ = ⟪x1 - x2, p1 - p2⟫ + ⟪(p1 - p2) - (x1 - x2), p1 - p2⟫ := by rw [inner_add_left]; simp
      _ ≤ ⟪x1 - x2, p1 - p2⟫ + 0 := add_le_add_left (by
          simp [sub_eq_add_neg] at h_sum ⊢
          exact h_sum
        ) _
      _ = ⟪x1 - x2, p1 - p2⟫ := add_zero _

  -- 使用 Cauchy-Schwarz 不等式：⟪a, b⟫ ≤ ‖a‖ * ‖b‖
  have h_cs : ⟪x1 - x2, p1 - p2⟫ ≤ ‖x1 - x2‖ * ‖p1 - p2‖ := real_inner_le_norm _ _

  -- 结合上述结果：‖p1 - p2‖² ≤ ‖x1 - x2‖ * ‖p1 - p2‖
  have h_final : ‖p1 - p2‖^2 ≤ ‖x1 - x2‖ * ‖p1 - p2‖ := h_fne.trans h_cs

  -- 最后消去两边的 ‖p1 - p2‖（处理范数为非负数的情况）
  exact (pow_two_le_mul_self_iff ‖p1 - p2‖ ‖x1 - x2‖).mp h_final
