import ComplexResponseOverlap
import NewtonExteriorResponse
import ExteriorContinuity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexExteriorIntegral
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ComplexGreenKernel
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

theorem hessian_continuousAt (z : ℂ) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (fun y => phiHessian z y i j) x := by
  have hr : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hr2 : (‖x‖ : ℂ)^2 ≠ 0 := pow_ne_zero 2 hr
  have hr3 : (‖x‖ : ℂ)^3 ≠ 0 := pow_ne_zero 3 hr
  have hp : (4 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hn : ContinuousAt (fun y : Space => (‖y‖ : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt
  have hi : ContinuousAt (fun y : Space => (y i : ℂ)) x := (coordinate i).continuous.continuousAt
  have hj : ContinuousAt (fun y : Space => (y j : ℂ)) x := (coordinate j).continuous.continuousAt
  unfold phiHessian radialDD radialD
  fun_prop (disch := assumption)

theorem remainder_continuousAt (z : ℂ) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (fun y => ComplexDynamicKernel.remainder z y i j) x := by
  unfold ComplexDynamicKernel.remainder ComplexDynamicKernel.dyadic
  exact (((continuousAt_const.mul (phi_contDiffAt z x hx).continuousAt).mul continuousAt_const).add
    (hessian_continuousAt z i j x hx)).sub (hessian_continuousAt 0 i j x hx)

theorem dyadic_continuousAt (z : ℂ) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (fun y => ComplexDynamicKernel.dyadic z y i j) x := by
  unfold ComplexDynamicKernel.dyadic
  exact ((continuousAt_const.mul (phi_contDiffAt z x hx).continuousAt).mul continuousAt_const).add
    (hessian_continuousAt z i j x hx)

def field (c : Coefficient) (z : ℂ) (u : VectorL2) : Field := fun x i =>
  ∑ j, ∫ y, DynamicVolume.source c u j y * ComplexDynamicKernel.dyadic z (x-y) i j

theorem response_exterior_ae (c : Coefficient) (z : ℂ) (S T R : ℝ) (hRS : S < R)
    (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) : ∀ᵐ x ∂(volume.restrict (closedBall 0 T)), R < ‖x‖ →
      ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i = field c z u x i := by
  let F := StaticCoefficient.sqrtMultiplier c u
  let ρ := DynamicVolume.source c u
  have hρ := DynamicVolume.source_integrable c u S hc
  have hzero := DynamicVolume.source_zero c u S hc
  have hF := StaticNewton.material_source_ae c u
  have hstatic := NewtonExteriorResponse.newton_ae_exterior F ρ hρ hF R S hRS hzero i
  have hdyn := ComplexResponseOverlap.dynamic_ae_on_ball z S T F ρ hρ hzero hF i
  have hadd := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (NewtonL2.newtonOperator F) (ComplexConvolutionAnalytic.operator z (T+S) F))
  have hcoord := NewtonL2.physicalCoordinate_ae (NewtonL2.newtonOperator F) i
  filter_upwards [ae_restrict_of_ae hstatic, hdyn, ae_restrict_of_ae hadd,
    ae_restrict_of_ae hcoord] with x hs hd ha hc' hr
  change (NewtonL2.newtonOperator F + ComplexConvolutionAnalytic.operator z (T+S) F)
    (VectorFourier.coordinateMap x) i = _
  rw [ha]
  change NewtonL2.newtonOperator F (VectorFourier.coordinateMap x) i +
    ComplexConvolutionAnalytic.operator z (T+S) F (VectorFourier.coordinateMap x) i = _
  rw [← hc', hs hr, hd]
  unfold field
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h1 := NewtonExteriorResponse.source_integrand_integrable (fun v => GreenKernel.phiHessian 0 v i j) (ρ j)
    (fun v hv => NewtonExterior.hessian_continuousAt 0 i j v hv) (hρ j) S (hzero j) x (lt_trans hRS hr)
  have h2 := NewtonExteriorResponse.source_integrand_integrable (fun v => ComplexDynamicKernel.remainder z v i j) (ρ j)
    (fun v hv => remainder_continuousAt z i j v hv) (hρ j) S (hzero j) x (lt_trans hRS hr)
  have h2' : Integrable (fun y => ComplexDynamicKernel.remainder z (x-y) i j * ρ j y) := by
    simpa only [mul_comm] using h2
  rw [← integral_add h1 h2']
  apply integral_congr_ae
  filter_upwards with y
  simp only [ComplexDynamicKernel.remainder]
  change ρ j y * GreenKernel.phiHessian 0 (x-y) i j +
    (ComplexDynamicKernel.dyadic z (x-y) i j - GreenKernel.phiHessian 0 (x-y) i j) * ρ j y = _
  ring

theorem field_continuousAt (c : Coefficient) (z : ℂ) (S : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (x : Space) (hx : S < ‖x‖) : ContinuousAt (field c z u) x := by
  apply continuousAt_pi.mpr
  intro i
  exact tendsto_finset_sum _ (fun j _ => ExteriorContinuity.response_continuousAt
    (fun v => ComplexDynamicKernel.dyadic z v i j) (DynamicVolume.source c u j)
    (fun v hv => dyadic_continuousAt z i j v hv)
    (DynamicVolume.source_integrable c u S hc j) S (DynamicVolume.source_zero c u S hc j) x hx)

#print axioms OQ14.ComplexExteriorIntegral.field_continuousAt
#print axioms OQ14.ComplexExteriorIntegral.dyadic_continuousAt
#print axioms OQ14.ComplexExteriorIntegral.response_exterior_ae
end OQ14.ComplexExteriorIntegral


