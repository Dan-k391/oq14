import Packet06CyclicDynamic
import ComplexDilationVolume

/-! Complex-frequency material volume block and derivative under actual cyclic rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06CyclicComplex
open Filter Set Metric Packet06CyclicL2 Packet06CyclicMaterial
open scoped Topology

def left (c : StaticCoefficient.Coefficient) (R : ℝ) (z : ℂ) : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  ComplexConvolutionAnalytic.volumeBlock (coefficient c) z R ∘L action

def right (c : StaticCoefficient.Coefficient) (R : ℝ) (z : ℂ) : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  action ∘L ComplexConvolutionAnalytic.volumeBlock c z R

theorem complex_conjugacy (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) (z : ℂ) :
    left c R z = right c R z := by
  have heq (t : ℝ) : left c R t = right c R t := by
    unfold left right
    rw [ComplexConvolutionAnalytic.volumeBlock_ofReal, ComplexConvolutionAnalytic.volumeBlock_ofReal]
    apply ContinuousLinearMap.ext
    intro u
    exact Packet06CyclicDynamic.real_volume_conjugacy c t R hc u
  have hl : AnalyticOnNhd ℂ (left c R) univ := by
    intro w hw
    exact (((ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient c) R hR).clm_comp
      (differentiable_const action)).analyticAt w)
  have hr : AnalyticOnNhd ℂ (right c R) univ := by
    intro w hw
    exact (((differentiable_const action).clm_comp
      (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR)).analyticAt w)
  have hclosure : (1 : ℂ) ∈ closure ({w | left c R w = right c R w} \ {(1 : ℂ)}) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let t : ℝ := 1+ε/2
    have ht : (t : ℂ) ≠ 1 := by
      have h : t ≠ 1 := by dsimp [t]; linarith
      exact_mod_cast h
    refine ⟨(t : ℂ), ⟨heq t, ht⟩, ?_⟩
    have hsub : (t : ℂ)-1 = ((ε/2 : ℝ) : ℂ) := by dsimp [t]; push_cast; ring
    rw [dist_comm, dist_eq_norm, hsub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact hl.eqOn_of_preconnected_of_mem_closure hr isPreconnected_univ (mem_univ 1) hclosure (mem_univ z)

theorem derivative_conjugacy (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : VectorFourier.VectorL2) :
    deriv (fun w => ComplexConvolutionAnalytic.volumeBlock (coefficient c) w R) z (action u) =
      action (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z u) := by
  have hfun : left c R = right c R := funext (complex_conjugacy c R hR hc)
  have hl := ((ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient c) R hR z).hasDerivAt).clm_comp
    (hasDerivAt_const z action)
  have hr := (hasDerivAt_const z action).clm_comp
    ((ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR z).hasDerivAt)
  change HasDerivAt (left c R) _ z at hl
  change HasDerivAt (right c R) _ z at hr
  rw [hfun] at hl
  have he := hl.unique hr
  have hv := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L u) he
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    zero_add, map_zero, add_zero] using hv

end OQ14.Packet06CyclicComplex
#print axioms OQ14.Packet06CyclicComplex.complex_conjugacy
#print axioms OQ14.Packet06CyclicComplex.derivative_conjugacy
