import Packet06AxialDynamicTransport
import ComplexDilationVolume

/-! Arbitrary-material complex-frequency volume transport by axial rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06AxialComplexTransport
open Filter Set Metric ModalAxialRotation Packet06AxialMaterialTransport Packet06AxialDynamicTransport
open scoped Topology
def left (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (z : ℂ) : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  ComplexConvolutionAnalytic.volumeBlock (coefficient θ c) z R ∘L (action θ)

def right (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (z : ℂ) : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 :=
  (action θ) ∘L ComplexConvolutionAnalytic.volumeBlock c z R

theorem complex_conjugacy (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) (z : ℂ) :
    left θ c R z = right θ c R z := by
  have heq (t : ℝ) : left θ c R t = right θ c R t := by
    unfold left right
    rw [ComplexConvolutionAnalytic.volumeBlock_ofReal, ComplexConvolutionAnalytic.volumeBlock_ofReal]
    apply ContinuousLinearMap.ext
    intro u
    unfold DynamicVolume.volumeBlock
    simp only [ContinuousLinearMap.sub_apply, map_sub]
    rw [StaticNewton.volumeBlock_eq,StaticNewton.volumeBlock_eq]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.sub_apply,map_sub]
    rw [← static_transport, ← weightedRemainder_transport c R hR hc θ t u]
  have hl : AnalyticOnNhd ℂ (left θ c R) univ := by
    intro w hw
    exact (((ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient θ c) R hR).clm_comp
      (differentiable_const (action θ))).analyticAt w)
  have hr : AnalyticOnNhd ℂ (right θ c R) univ := by
    intro w hw
    exact (((differentiable_const (action θ)).clm_comp
      (ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR)).analyticAt w)
  have hclosure : (1 : ℂ) ∈ closure ({w | left θ c R w = right θ c R w} \ {(1 : ℂ)}) := by
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

theorem derivative_conjugacy (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : VectorFourier.VectorL2) :
    deriv (fun w => ComplexConvolutionAnalytic.volumeBlock (coefficient θ c) w R) z (action θ u) =
      action θ (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock c w R) z u) := by
  have hfun : left θ c R = right θ c R := funext (complex_conjugacy θ c R hR hc)
  have hl := ((ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient θ c) R hR z).hasDerivAt).clm_comp
    (hasDerivAt_const z (action θ))
  have hr := (hasDerivAt_const z (action θ)).clm_comp
    ((ComplexConvolutionAnalytic.volumeBlock_differentiable c R hR z).hasDerivAt)
  change HasDerivAt (left θ c R) _ z at hl
  change HasDerivAt (right θ c R) _ z at hr
  rw [hfun] at hl
  have he := hl.unique hr
  have hv := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L u) he
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    zero_add, map_zero, add_zero] using hv


end OQ14.Packet06AxialComplexTransport
#print axioms OQ14.Packet06AxialComplexTransport.complex_conjugacy
#print axioms OQ14.Packet06AxialComplexTransport.derivative_conjugacy
