import ComplexKernelResponse
import MaterialVolumeConverse

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexResponseAnalytic
open MeasureTheory Metric OQ14.Maxwell OQ14.ComplexKernelResponse
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem response_differentiable (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (u : VectorL2) :
    Differentiable ℂ (fun z => response c z R u) := by
  unfold response
  exact (differentiable_const _).add
    ((ComplexConvolutionAnalytic.operator_differentiable (2*R) (by positivity)).clm_apply
      (differentiable_const _))

theorem response_analyticAt (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (u : VectorL2) (z : ℂ) :
    AnalyticAt ℂ (fun w => response c w R u) z :=
  (response_differentiable c R hR u).analyticAt z

theorem response_ofReal (c : Coefficient) (k R : ℝ) (u : VectorL2) :
    response c (k : ℂ) R u = NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u) +
      DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c u) := by
  simp [response, ComplexConvolutionAnalytic.operator_ofReal]

theorem kernel_source_relation (c : Coefficient) (z : ℂ) (R : ℝ) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) (i : Fin 3) :
    DynamicVolume.source c u i =ᵐ[volume] fun x =>
      (c.value (VectorFourier.coordinateMap x) : ℂ) *
        response c z R u (VectorFourier.coordinateMap x) i := by
  apply MaterialVolumeConverse.source_from_weighted c u
    (fun x i => response c z R u (VectorFourier.coordinateMap x) i) ?_ i
  intro j
  filter_upwards [kernel_coordinate_ae c z R u hker] with x hx
  exact congrFun hx j

#print axioms OQ14.ComplexResponseAnalytic.response_differentiable
#print axioms OQ14.ComplexResponseAnalytic.response_analyticAt
#print axioms OQ14.ComplexResponseAnalytic.response_ofReal
#print axioms OQ14.ComplexResponseAnalytic.kernel_source_relation
end OQ14.ComplexResponseAnalytic

