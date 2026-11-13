import Packet06TranslationDynamic
import ComplexDilationVolume

/-! Complex-frequency material volume block and derivative under actual cyclic rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06TranslationComplex
open Filter Set Metric Packet06TranslationL2 Packet06TranslationMaterial
open scoped Topology

def left (a : Maxwell.Space) (c : StaticCoefficient.Coefficient) (R : ℝ) (z : ℂ) : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  ComplexConvolutionAnalytic.volumeBlock (coefficient a c) z (R+‖a‖) ∘L action a

def right (a : Maxwell.Space) (c : StaticCoefficient.Coefficient) (R : ℝ) (z : ℂ) : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  action a ∘L ComplexConvolutionAnalytic.volumeBlock c z R

theorem complex_conjugacy (a : Maxwell.Space) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) (z : ℂ) :
    left a c R z = right a c R z := by
  have heq (t : ℝ) : left a c R t = right a c R t := by
    unfold left right
    rw [ComplexConvolutionAnalytic.volumeBlock_ofReal, ComplexConvolutionAnalytic.volumeBlock_ofReal]
    apply ContinuousLinearMap.ext
    intro u
    exact Packet06TranslationDynamic.real_volume_conjugacy a c t R hc u
  have hl : AnalyticOnNhd ℂ (left a c R) univ := by
    intro w hw
    exact (((ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient a c) (R+‖a‖) (by positivity)).clm_comp
      (differentiable_const (action a))).analyticAt w)
  have hr : AnalyticOnNhd ℂ (right a c R) univ := by
    intro w hw
    exact (((differentiable_const (action a)).clm_comp
      (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR)).analyticAt w)
  have hclosure : (1 : ℂ) ∈ closure ({w | left a c R w = right a c R w} \ {(1 : ℂ)}) := by
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

theorem derivative_conjugacy (a : Maxwell.Space) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : VectorFourier.VectorL2) :
    deriv (fun w => ComplexConvolutionAnalytic.volumeBlock (coefficient a c) w (R+‖a‖)) z (action a u) =
      action a (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z u) := by
  have hfun : left a c R = right a c R := funext (complex_conjugacy a c R hR hc)
  have hl := ((ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient a c) (R+‖a‖) (by positivity) z).hasDerivAt).clm_comp
    (hasDerivAt_const z (action a))
  have hr := (hasDerivAt_const z (action a)).clm_comp
    ((ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR z).hasDerivAt)
  change HasDerivAt (left a c R) _ z at hl
  change HasDerivAt (right a c R) _ z at hr
  rw [hfun] at hl
  have he := hl.unique hr
  have hv := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L u) he
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    zero_add, map_zero, add_zero] using hv

end OQ14.Packet06TranslationComplex
#print axioms OQ14.Packet06TranslationComplex.complex_conjugacy
#print axioms OQ14.Packet06TranslationComplex.derivative_conjugacy
