import ComplexMagneticOperator
import DynamicVolume

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexMagneticResponse
open Complex MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.ComplexGreenKernel
  OQ14.ComplexMagneticOperator OQ14.DynamicConvolution
open OQ14.WeakCurl (next previous)
open scoped Topology
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev ScalarL2 := FourierL2.ScalarL2

def response (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2) (i : Fin 3) : ScalarL2 :=
  (-(I*z)) • (entry z (T+S) (next i) (component (previous i) (StaticCoefficient.sqrtMultiplier c u)) -
    entry z (T+S) (previous i) (component (next i) (StaticCoefficient.sqrtMultiplier c u)))

theorem response_differentiable (c : Coefficient) (S T : ℝ) (u : VectorL2) (i : Fin 3) :
    Differentiable ℂ (fun z => response c z S T u i) := by
  unfold response
  apply ((differentiable_const I).mul differentiable_id).neg.smul
  exact ((entry_differentiable (T+S) (next i)).clm_apply (differentiable_const _)).sub
    ((entry_differentiable (T+S) (previous i)).clm_apply (differentiable_const _))

theorem truncated_source (z : ℂ) (K : ℝ) (F : VectorL2) (ρ : Maxwell.Space → ℂ) (j : Fin 3)
    (hF : (NewtonL2.physicalCoordinate F j : Maxwell.Space → ℂ) =ᵐ[volume] ρ) (i : Fin 3) (x : Maxwell.Space) :
    HeatFourier.convolution (fullKernel z K i) (component j F) x =
      ∫ y, fullKernel z K i (x-y) * ρ y := by
  change MeasureTheory.convolution (fullKernel z K i) (component j F)
    (ContinuousLinearMap.mul ℂ ℂ) volume x = _
  rw [MeasureTheory.convolution_mul_swap]
  apply integral_congr_ae
  filter_upwards [hF] with y hy
  rw [component_apply, hy]

theorem kernel_source (z : ℂ) (S T : ℝ) (ρ : Maxwell.Space → ℂ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (j : Fin 3)
    (x y : Maxwell.Space) (hx : x ∈ closedBall 0 T) :
    fullKernel z (T+S) j (x-y) * ρ y = phiGradient z (x-y) j * ρ y := by
  by_cases hy : y ∈ closedBall (0 : Maxwell.Space) S
  · have hxy : x-y ∈ closedBall (0 : Maxwell.Space) (T+S) := by
      simp only [mem_closedBall, dist_zero_right] at hx hy ⊢
      exact (norm_sub_le _ _).trans (add_le_add hx hy)
    simp [fullKernel, hxy]
  · simp [hc y hy]

theorem gradient_ae_on_ball (z : ℂ) (S T : ℝ) (F : VectorL2)
    (ρ : Fin 3 → Maxwell.Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Maxwell.Space → ℂ) =ᵐ[volume] ρ j)
    (i j : Fin 3) :
    (entry z (T+S) i (component j F) : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 T)]
      KernelConvolution.response (fun x => phiGradient z x i) (ρ j) := by
  have hd := entry_ae z (T+S) i (component j F) ((hρ j).congr (hF j).symm)
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_closedBall] with x hx hxb
  rw [hx, truncated_source z (T+S) F (ρ j) j (hF j) i x]
  unfold KernelConvolution.response
  apply integral_congr_ae
  filter_upwards with y
  rw [kernel_source z S T (ρ j) (hc j) i x y hxb, mul_comm]

theorem response_actual (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (response c z S T u i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 T)]
      fun x => ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x i := by
  let F := StaticCoefficient.sqrtMultiplier c u
  let ρ := DynamicVolume.source c u
  have hρ := DynamicVolume.source_integrable c u S hc
  have hzero := DynamicVolume.source_zero c u S hc
  have hF := StaticNewton.material_source_ae c u
  filter_upwards [gradient_ae_on_ball z S T F ρ hρ hzero hF (next i) (previous i),
    gradient_ae_on_ball z S T F ρ hρ hzero hF (previous i) (next i),
    ae_restrict_of_ae (Lp.coeFn_sub (entry z (T+S) (next i) (component (previous i) F))
      (entry z (T+S) (previous i) (component (next i) F))),
    ae_restrict_of_ae (Lp.coeFn_smul (-(I*z)) (entry z (T+S) (next i) (component (previous i) F) -
      entry z (T+S) (previous i) (component (next i) F)))] with x h1 h2 hsub hsm
  change ((-(I*z)) • (entry z (T+S) (next i) (component (previous i) F) -
    entry z (T+S) (previous i) (component (next i) F))) x = _
  rw [hsm, Pi.smul_apply, hsub, Pi.sub_apply, h1, h2]
  rfl

#print axioms OQ14.ComplexMagneticResponse.response_differentiable
#print axioms OQ14.ComplexMagneticResponse.response_actual
end OQ14.ComplexMagneticResponse

