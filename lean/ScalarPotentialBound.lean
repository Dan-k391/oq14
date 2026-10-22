import L2KernelCompact
import LocalConvolution
import KernelIntegrability

/-! Actual compact L2 source potentials are continuous and locally bounded,
with a scalar Green bound independent of the real frequency. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ScalarPotentialBound
open MeasureTheory Metric Set OQ14.Maxwell OQ14.KernelIntegrability
open scoped Topology

abbrev ScalarL2 := FourierL2.ScalarL2

theorem cutoff_memLp (k T : ℝ) :
    MemLp (LocalConvolution.kernel (GreenKernel.phi k) T) 2 (volume : Measure Space) :=
  (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (phi_memLp_two_ball k T)

def cutoff (k T : ℝ) : ScalarL2 :=
  (cutoff_memLp k T).toLp (LocalConvolution.kernel (GreenKernel.phi k) T)

theorem cutoff_ae (k T : ℝ) :
    (cutoff k T : Space → ℂ) =ᵐ[volume] LocalConvolution.kernel (GreenKernel.phi k) T :=
  (cutoff_memLp k T).coeFn_toLp

theorem cutoff_norm (k T : ℝ) : ‖cutoff k T‖=‖cutoff 0 T‖ := by
  simp only [cutoff,Lp.norm_toLp]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) T
  · simp only [LocalConvolution.kernel,indicator_of_mem hx,phi_norm]
  · simp only [LocalConvolution.kernel,indicator_of_not_mem hx]

theorem value_eq_response (k R S : ℝ) (ρ : Space → ℂ) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y=0) (x : Space) (hx : x ∈ closedBall 0 R) :
    L2KernelCompact.value (cutoff k (R+S)) F x=KernelConvolution.response (GreenKernel.phi k) ρ x := by
  rw [L2KernelCompact.value_integral]
  apply integral_congr_ae
  have hq := (Measure.measurePreserving_sub_left (volume : Measure Space) x).quasiMeasurePreserving.ae
    (cutoff_ae k (R+S))
  filter_upwards [hF,hq] with y hy hqy
  rw [hy,hqy]
  exact LocalConvolution.kernel_source_eq (GreenKernel.phi k) ρ R S hc x y hx

theorem response_integrable (k R S : ℝ) (ρ : Space → ℂ) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y=0) (x : Space) (hx : x ∈ closedBall 0 R) :
    Integrable (fun y => ρ y*GreenKernel.phi k (x-y)) := by
  apply (L2KernelCompact.value_integrable (cutoff k (R+S)) F x).congr
  have hq := (Measure.measurePreserving_sub_left (volume : Measure Space) x).quasiMeasurePreserving.ae
    (cutoff_ae k (R+S))
  filter_upwards [hF,hq] with y hy hqy
  rw [hy,hqy]
  exact LocalConvolution.kernel_source_eq (GreenKernel.phi k) ρ R S hc x y hx

theorem response_bound (k R S : ℝ) (ρ : Space → ℂ) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y=0) (x : Space) (hx : x ∈ closedBall 0 R) :
    ‖KernelConvolution.response (GreenKernel.phi k) ρ x‖ ≤ ‖F‖*‖cutoff 0 (R+S)‖ := by
  rw [← value_eq_response k R S ρ F hF hc x hx,← cutoff_norm k (R+S)]
  exact L2KernelCompact.value_norm_le _ _ _

theorem response_continuous (k S : ℝ) (ρ : Space → ℂ) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y=0) :
    Continuous (KernelConvolution.response (GreenKernel.phi k) ρ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have he : KernelConvolution.response (GreenKernel.phi k) ρ =ᶠ[nhds x]
      L2KernelCompact.value (cutoff k (‖x‖+1+S)) F := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    have hn : ‖y‖ ≤ ‖x‖+1 := by
      have ht := norm_add_le (y-x) x
      rw [sub_add_cancel] at ht
      have hd : ‖y-x‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hy
      linarith
    exact (value_eq_response k (‖x‖+1) S ρ F hF hc y (by simpa only [mem_closedBall,dist_zero_right] using hn)).symm
  exact (L2KernelCompact.value_continuous _ F).continuousAt.congr he.symm

theorem scaled_response_bound (k R S : ℝ) (ρ : Space → ℂ) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y=0) (x : Space) (hx : x ∈ closedBall 0 R) :
    ‖(k : ℂ)^2*KernelConvolution.response (GreenKernel.phi k) ρ x‖ ≤
      k^2*‖F‖*‖cutoff 0 (R+S)‖ := by
  rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact (mul_le_mul_of_nonneg_left (response_bound k R S ρ F hF hc x hx) (sq_nonneg k)).trans_eq
    (mul_assoc _ _ _).symm

end OQ14.ScalarPotentialBound

#print axioms OQ14.ScalarPotentialBound.cutoff_memLp
#print axioms OQ14.ScalarPotentialBound.cutoff_ae
#print axioms OQ14.ScalarPotentialBound.cutoff_norm
#print axioms OQ14.ScalarPotentialBound.value_eq_response
#print axioms OQ14.ScalarPotentialBound.response_integrable
#print axioms OQ14.ScalarPotentialBound.response_bound
#print axioms OQ14.ScalarPotentialBound.response_continuous
#print axioms OQ14.ScalarPotentialBound.scaled_response_bound
