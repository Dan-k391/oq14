import Packet06ComplexScalarKernel
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexScalarPotential
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06ComplexScalarKernel
open scoped Topology
abbrev ScalarL2 := FourierL2.ScalarL2

def cutoff (z : ℂ) (T : ℝ) : ScalarL2 :=
  ((memLp_indicator_iff_restrict measurableSet_closedBall).mpr (phi_memLp_two_ball z T)).toLp
    (LocalConvolution.kernel (ComplexGreenKernel.phi z) T)

theorem cutoff_ae (z : ℂ) (T : ℝ) :
    (cutoff z T : Space → ℂ) =ᵐ[volume] LocalConvolution.kernel (ComplexGreenKernel.phi z) T :=
  ((memLp_indicator_iff_restrict measurableSet_closedBall).mpr (phi_memLp_two_ball z T)).coeFn_toLp

theorem value_eq_response (z : ℂ) (R S : ℝ) (ρ : Space → ℂ) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y=0) (x : Space) (hx : x ∈ closedBall 0 R) :
    L2KernelCompact.value (cutoff z (R+S)) F x=KernelConvolution.response (ComplexGreenKernel.phi z) ρ x := by
  rw [L2KernelCompact.value_integral]
  apply integral_congr_ae
  have hq := (Measure.measurePreserving_sub_left (volume : Measure Space) x).quasiMeasurePreserving.ae
    (cutoff_ae z (R+S))
  filter_upwards [hF,hq] with y hy hqy
  rw [hy,hqy]
  exact LocalConvolution.kernel_source_eq (ComplexGreenKernel.phi z) ρ R S hc x y hx

theorem response_continuous (z : ℂ) (S : ℝ) (ρ : Space → ℂ) (F : ScalarL2)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y=0) :
    Continuous (KernelConvolution.response (ComplexGreenKernel.phi z) ρ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have he : KernelConvolution.response (ComplexGreenKernel.phi z) ρ =ᶠ[nhds x]
      L2KernelCompact.value (cutoff z (‖x‖+1+S)) F := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    have hn : ‖y‖ ≤ ‖x‖+1 := by
      have ht := norm_add_le (y-x) x
      rw [sub_add_cancel] at ht
      have hd : ‖y-x‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hy
      linarith
    exact (value_eq_response z (‖x‖+1) S ρ F hF hc y (by simpa only [mem_closedBall,dist_zero_right] using hn)).symm
  exact (L2KernelCompact.value_continuous _ F).continuousAt.congr he.symm
#print axioms OQ14.Packet06ComplexScalarPotential.cutoff_ae
#print axioms OQ14.Packet06ComplexScalarPotential.value_eq_response
#print axioms OQ14.Packet06ComplexScalarPotential.response_continuous
end OQ14.Packet06ComplexScalarPotential
