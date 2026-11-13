import Packet06WeightedTransport
import ComplexResponseOverlap

/-! Actual truncated local volume operators. Their global L2 representatives
are only identified with the physical field on the stated observation ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace OQ14.Packet06LocalPencil
open MeasureTheory Metric
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

def kernel (z : ℂ) (S T : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  NewtonL2.newtonOperator + ComplexConvolutionAnalytic.operator z (T+S)

def response (c : Coefficient) (z : ℂ) (S T : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  (kernel z S T).comp (StaticCoefficient.sqrtMultiplier c)

theorem response_actual (c : Coefficient) (z : ℂ) (S T : ℝ) (u : VectorL2) :
    response c z S T u = ComplexExteriorResponse.response c z S T u := rfl

theorem kernel_analyticAt (S T : ℝ) (hST : 0 ≤ T+S) (z : ℂ) :
    AnalyticAt ℂ (fun w => kernel w S T) z := by
  exact (analyticAt_const).add (ComplexConvolutionAnalytic.operator_analyticAt z (T+S) hST)

theorem response_analyticAt (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S) (z : ℂ) :
    AnalyticAt ℂ (fun w => response c w S T) z := by
  exact (((ContinuousLinearMap.compL ℂ VectorL2 VectorL2 VectorL2).flip
    (StaticCoefficient.sqrtMultiplier c)).analyticAt (kernel z S T)).comp
      (f := fun w : ℂ => kernel w S T) (kernel_analyticAt S T hST z)

theorem weighted_block_eq (c : Coefficient) (z : ℂ) (R : ℝ) :
    ComplexConvolutionAnalytic.volumeBlock c z R =
      1-StaticCoefficient.sqrtMultiplier c*kernel z R R*StaticCoefficient.sqrtMultiplier c := by
  apply ContinuousLinearMap.ext
  intro u
  change (u-StaticCoefficient.sqrtMultiplier c (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u)))-
    StaticCoefficient.sqrtMultiplier c (ComplexConvolutionAnalytic.operator z (2*R) (StaticCoefficient.sqrtMultiplier c u)) =
    u-StaticCoefficient.sqrtMultiplier c
      ((NewtonL2.newtonOperator+ComplexConvolutionAnalytic.operator z (R+R)) (StaticCoefficient.sqrtMultiplier c u))
  rw [ContinuousLinearMap.add_apply,map_add,show R+R=2*R by ring]
  abel

def unweighted (c : Coefficient) (z : ℂ) (R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  1-kernel z R R*StaticCoefficient.sqrtMultiplier c*StaticCoefficient.sqrtMultiplier c

theorem unweighted_analyticAt (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) :
    AnalyticAt ℂ (fun w => unweighted c w R) z := by
  apply AnalyticAt.sub analyticAt_const
  exact ((kernel_analyticAt R R (by positivity) z).mul analyticAt_const).mul analyticAt_const

theorem actual_inverse_transport (c : Coefficient) (z : ℂ) (R : ℝ)
    (hu : IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R)) :
    IsUnit (unweighted c z R) ∧
      Ring.inverse (unweighted c z R) =
        1+kernel z R R*StaticCoefficient.sqrtMultiplier c*
          Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R)*StaticCoefficient.sqrtMultiplier c := by
  rw [weighted_block_eq] at hu ⊢
  exact Packet06WeightedTransport.weighted_inverse_formula _ _ hu

theorem actual_kernel_transport (c : Coefficient) (z : ℂ) (R : ℝ) (u : VectorL2)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) :
    unweighted c z R (response c z R R u) = 0 ∧
      StaticCoefficient.sqrtMultiplier c (response c z R R u) = u := by
  rw [weighted_block_eq] at hu
  exact Packet06WeightedTransport.kernel_backward _ _ _ hu

theorem response_nonzero (c : Coefficient) (z : ℂ) (R : ℝ) (u : VectorL2)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) (hne : u ≠ 0) :
    response c z R R u ≠ 0 := by
  intro h
  have hh := (actual_kernel_transport c z R u hu).2
  rw [h,map_zero] at hh
  exact hne hh.symm

theorem response_overlap (c : Coefficient) (z : ℂ) (S T U : ℝ) (hTU : T ≤ U) (u : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x => response c z S T u (VectorFourier.coordinateMap x) i) =ᵐ[volume.restrict (closedBall 0 T)]
      fun x => response c z S U u (VectorFourier.coordinateMap x) i :=
  ComplexResponseOverlap.response_overlap c z S T U hTU u hc i

end OQ14.Packet06LocalPencil
#print axioms OQ14.Packet06LocalPencil.response_actual
#print axioms OQ14.Packet06LocalPencil.kernel_analyticAt
#print axioms OQ14.Packet06LocalPencil.response_analyticAt
#print axioms OQ14.Packet06LocalPencil.weighted_block_eq
#print axioms OQ14.Packet06LocalPencil.unweighted_analyticAt
#print axioms OQ14.Packet06LocalPencil.actual_inverse_transport
#print axioms OQ14.Packet06LocalPencil.actual_kernel_transport
#print axioms OQ14.Packet06LocalPencil.response_nonzero
#print axioms OQ14.Packet06LocalPencil.response_overlap
