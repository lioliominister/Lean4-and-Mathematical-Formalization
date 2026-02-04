import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Basic

variable {H : Type*} [NormedAddCommGroup H] [CompleteSpace H] [InnerProductSpace ℝ H]
variable {C : Set H}

def is_proj (C : Set H) (x x' : H) : Prop := 
  x' ∈ C ∧ ‖x - x'‖ = ⨅ (w : ↑C), ‖x - ↑w‖





lemma proj_opt_cond (conv_c : Convex ℝ C) (close_c : IsClosed C) 
    {x x' : H} (h_proj : is_proj C x x') :
    ∀ w ∈ C, inner ℝ (x - x') (w - x') ≤ 0 := by
  rcases h_proj with ⟨x'c, h_min⟩
  --关于实内积空间投影的等价性定理
  exact (norm_eq_iInf_iff_real_inner_le_zero conv_c x'c).1 h_min


theorem proj_step_dist_decay (conv_c : Convex ℝ C) (close_c : IsClosed C)
    {x x' z : H} (h_proj : is_proj C x x') (hz : z ∈ C) :
    ‖x' - z‖^2 ≤ ‖x - z‖^2 - ‖x - x'‖^2 := by
  
  have h_opt := proj_opt_cond conv_c close_c h_proj z hz
  

  have h_expand : ‖x - z‖^2 = ‖x - x'‖^2 + ‖x' - z‖^2 + 2 * inner ℝ (x - x') (x' - z) := by

    let h := norm_add_sq_real (x - x') (x' - z)
    have : (x - x') + (x' - z) = x - z := by abel
    rw [← this]
    exact h

  have h_inner_nonneg : 0 ≤ inner ℝ (x - x') (x' - z) := by
    rw [← neg_sub z x', inner_neg_right]
    linarith [h_opt]

  calc ‖x' - z‖^2 
    _ ≤ ‖x' - z‖^2 + ‖x - x'‖^2 + 2 * inner ℝ (x - x') (x' - z) := by
        -- 利用 ‖x - x'‖² ≥ 0 和 2 * inner ≥ 0
        have : 0 ≤ ‖x - x'‖^2 + 2 * inner ℝ (x - x') (x' - z) := by
          have : 0 ≤ ‖x - x'‖^2 := sq_nonneg _
          linarith
        linarith
    _ = ‖x - z‖^2 := by rw [← h_expand]
  
  linarith
