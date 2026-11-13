import Packet05GraphH2Pullback

/-! Quantitative L² estimates for the exact graph H² pullback. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05GraphH2Norm
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphH2Pullback
  OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05BoundedWeakMultiplier
  OQ14.Packet05LocalizedAnisotropic
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem bounded_multiply_norm (a : Space → ℂ) (ha : MemLp a ⊤ volume)
    (u : L2Scalar) (K : ℝ) (hK : ∀ x, ‖a x‖ ≤ K) :
    ‖boundedMultiply a ha u‖ ≤ K*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedMultiply_ae a ha u] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (hK x) (norm_nonneg _)

theorem slope_multiply_norm (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    (B : ℝ) (hB : ∀ x, ‖slopeC g i x‖ ≤ B) (u : L2Scalar) :
    ‖slopeMul g hg i B hB u‖ ≤ B*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [slopeMul_ae g hg i B hB u] with x hx
  rw [hx,norm_mul]
  exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

theorem pulled_gradient_norm (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (U : L2Vector)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) (i : Fin 3) :
    ‖pulledGradient g hg U B hB i‖ ≤ ‖U i‖ + B i*‖U 2‖ := by
  have h := slope_multiply_norm g hg i (B i) (hB i) (pullback g hg.continuous (U 2))
  rw [pullback_norm] at h
  unfold pulledGradient
  exact (norm_add_le _ _).trans (by rw [pullback_norm]; linarith)

theorem graph_pullback_h2_bounded (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (u : L2Scalar)
    (G : L2Vector) (H : Fin 3 → L2Vector)
    (hG : ∀ i, HasWeakPartial u (G i) i) (hH : ∀ i j, HasWeakPartial (G i) (H i j) j)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i)
    (hdi : ∀ i j, MemLp (fun x => dcoord (slopeC g i) x j) ⊤ volume)
    (L : Fin 3 → Fin 3 → ℝ) (hL : ∀ i j x, ‖dcoord (slopeC g i) x j‖ ≤ L i j) :
    ∃ K : Fin 3 → Fin 3 → L2Scalar,
      (∀ i, HasWeakPartial (pullback g hg.continuous u) (pulledGradient g hg G B hB i) i) ∧
      (∀ i j, HasWeakPartial (pulledGradient g hg G B hB i) (K i j) j) ∧
      (∀ i j, ‖K i j‖ ≤ ‖H i j‖ + B j*‖H i 2‖ +
        B i*(‖H 2 j‖+B j*‖H 2 2‖) + L i j*‖G 2‖) := by
  have hfirst := graph_pullback_h1 g hg u G hG B hB
  have hp (i j : Fin 3) := graph_pullback_h1 g hg (G i) (H i) (hH i) B hB j
  have hs (i j : Fin 3) : HasWeakPartial
      (slopeMul g hg i (B i) (hB i) (pullback g hg.continuous (G 2)))
      (boundedMultiply (slopeC g i) (slopeC_memLp_top g hg i (B i) (hB i))
        (pulledGradient g hg (H 2) B hB j) +
        boundedMultiply (fun x => dcoord (slopeC g i) x j) (hdi i j)
          (pullback g hg.continuous (G 2))) j := by
    exact bounded_multiplier_weak_partial _ (slopeC_contDiff g hg i) _ j (hdi i j) _ _ (hp 2 j)
  let K (i j : Fin 3) := pulledGradient g hg (H i) B hB j +
    (boundedMultiply (slopeC g i) (slopeC_memLp_top g hg i (B i) (hB i))
        (pulledGradient g hg (H 2) B hB j) +
      boundedMultiply (fun x => dcoord (slopeC g i) x j) (hdi i j)
        (pullback g hg.continuous (G 2)))
  refine ⟨K,hfirst,?_,?_⟩
  · intro i j
    exact weak_partial_add _ _ _ _ j (hp i j) (hs i j)
  · intro i j
    have hBi : 0 ≤ B i := (norm_nonneg _).trans (hB i 0)
    have h1 := pulled_gradient_norm g hg (H i) B hB j
    have h2 := pulled_gradient_norm g hg (H 2) B hB j
    have h3 := bounded_multiply_norm (slopeC g i) (slopeC_memLp_top g hg i (B i) (hB i))
      (pulledGradient g hg (H 2) B hB j) (B i) (hB i)
    have h4 := bounded_multiply_norm (fun x => dcoord (slopeC g i) x j) (hdi i j)
      (pullback g hg.continuous (G 2)) (L i j) (hL i j)
    rw [pullback_norm] at h4
    have h2' := mul_le_mul_of_nonneg_left h2 hBi
    change ‖pulledGradient g hg (H i) B hB j + _‖ ≤ _
    have hn := norm_add_le
      (boundedMultiply (slopeC g i) (slopeC_memLp_top g hg i (B i) (hB i)) (pulledGradient g hg (H 2) B hB j))
      (boundedMultiply (fun x => dcoord (slopeC g i) x j) (hdi i j) (pullback g hg.continuous (G 2)))
    exact (norm_add_le _ _).trans (by linarith)

end OQ14.Packet05GraphH2Norm
#print axioms OQ14.Packet05GraphH2Norm.bounded_multiply_norm
#print axioms OQ14.Packet05GraphH2Norm.slope_multiply_norm
#print axioms OQ14.Packet05GraphH2Norm.pulled_gradient_norm
#print axioms OQ14.Packet05GraphH2Norm.graph_pullback_h2_bounded
