import Packet06GreenHolderTransfer
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenHolderSourceRows
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06ComplexScalarPotential
open OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakTranslations OQ14.WeakCompactness

/-- Restrict the kernel row to the fixed source ball, eliminating any moving cutoff boundary. -/
def sourceRow (z : ℂ) (R S : ℝ) (x : Space) : ScalarL2 :=
  let q := L2KernelCompact.row (cutoff z (R+S)) x
  ((Lp.memLp q).indicator measurableSet_closedBall).toLp
    ((closedBall (0 : Space) S).indicator (q : Space → ℂ))

theorem sourceRow_ae (z : ℂ) (R S : ℝ) (x : Space) :
    (sourceRow z R S x : Space → ℂ) =ᵐ[volume]
      (closedBall (0 : Space) S).indicator (fun y => (cutoff z (R+S)) (x-y)) := by
  have h : (sourceRow z R S x : Space → ℂ) =ᵐ[volume]
      (closedBall (0 : Space) S).indicator (L2KernelCompact.row (cutoff z (R+S)) x : Space → ℂ) :=
    ((Lp.memLp (L2KernelCompact.row (cutoff z (R+S)) x)).indicator
      measurableSet_closedBall).coeFn_toLp
  filter_upwards [h, L2KernelCompact.row_ae (cutoff z (R+S)) x] with y hy hr
  rw [hy]
  by_cases hs : y ∈ closedBall (0 : Space) S
  · simp only [indicator_of_mem hs, hr]
  · simp only [indicator_of_not_mem hs]

/-- On the observation ball these restricted rows are the literal Green kernel. -/
theorem sourceRow_actual_ae (z : ℂ) (R S : ℝ) (x : Space)
    (hx : x ∈ closedBall 0 R) :
    (sourceRow z R S x : Space → ℂ) =ᵐ[volume]
      (closedBall (0 : Space) S).indicator (fun y => ComplexGreenKernel.phi z (x-y)) := by
  have hc := (Measure.measurePreserving_sub_left (volume : Measure Space) x).quasiMeasurePreserving.ae
    (cutoff_ae z (R+S))
  filter_upwards [sourceRow_ae z R S x, hc] with y hy hcut
  rw [hy]
  by_cases hs : y ∈ closedBall (0 : Space) S
  · have hxy : x-y ∈ closedBall (0 : Space) (R+S) := by
      simp only [mem_closedBall, dist_zero_right] at hx hs ⊢
      exact (norm_sub_le _ _).trans (add_le_add hx hs)
    simp only [indicator_of_mem hs, hcut, LocalConvolution.kernel, indicator_of_mem hxy]
  · simp only [indicator_of_not_mem hs]
theorem scalarProduct_sourceRow (z : ℂ) (R S : ℝ) (ρ : Space → ℂ) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (x : Space) :
    scalarProduct F (sourceRow z R S x) = L2KernelCompact.value (cutoff z (R+S)) F x := by
  rw [scalarProduct_integral, L2KernelCompact.value_integral]
  apply integral_congr_ae
  filter_upwards [hF, sourceRow_ae z R S x, L2KernelCompact.row_ae (cutoff z (R+S)) x] with y hf hs hr
  rw [hs]
  by_cases hy : y ∈ closedBall (0 : Space) S
  · simp only [indicator_of_mem hy]
  · rw [indicator_of_not_mem hy, mul_zero, hf, hc y hy, zero_mul]

theorem response_difference_of_sourceRow_bound (z : ℂ) (R S : ℝ) (ρ : Space → ℂ)
    (F : ScalarL2) (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (x y : Space) (hx : x ∈ closedBall 0 R) (hy : y ∈ closedBall 0 R)
    (C : ℝ) (hm : dist (sourceRow z R S x) (sourceRow z R S y) ≤ C * Real.sqrt (dist x y)) :
    dist (z^2 * KernelConvolution.response (ComplexGreenKernel.phi z) ρ x)
      (z^2 * KernelConvolution.response (ComplexGreenKernel.phi z) ρ y) ≤
      ‖z‖^2 * ‖F‖ * C * Real.sqrt (dist x y) := by
  rw [← value_eq_response z R S ρ F hF hc x hx,
    ← value_eq_response z R S ρ F hF hc y hy]
  rw [← scalarProduct_sourceRow z R S ρ F hF hc x,
    ← scalarProduct_sourceRow z R S ρ F hF hc y]
  rw [dist_eq_norm, ← mul_sub, norm_mul, norm_pow, ← map_sub]
  have h := scalarProduct_norm_le F (sourceRow z R S x - sourceRow z R S y)
  rw [← dist_eq_norm] at h
  have h' := h.trans (mul_le_mul_of_nonneg_left hm (norm_nonneg F))
  calc
    ‖z‖ ^ 2 * ‖scalarProduct F (sourceRow z R S x - sourceRow z R S y)‖ ≤
        ‖z‖ ^ 2 * (‖F‖ * (C * Real.sqrt (dist x y))) :=
          mul_le_mul_of_nonneg_left h' (sq_nonneg ‖z‖)
    _ = _ := by ring

#print axioms OQ14.Packet06GreenHolderSourceRows.sourceRow_ae
#print axioms OQ14.Packet06GreenHolderSourceRows.sourceRow_actual_ae
#print axioms OQ14.Packet06GreenHolderSourceRows.scalarProduct_sourceRow
#print axioms OQ14.Packet06GreenHolderSourceRows.response_difference_of_sourceRow_bound
end OQ14.Packet06GreenHolderSourceRows
