import Packet06GreenSource
import Packet06PhysicalNormalization

/-! Physical integral dictionary for the direct electric Green source equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06GreenPhysical
open MeasureTheory Metric Packet06GreenSource ComplexResponseTests DynamicSource
open scoped SchwartzMap
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

theorem dielectric_test_integral (c : Coefficient) (F : VectorL2)
    (i : Fin 3) (f : 𝓢(Maxwell.Space, ℂ)) :
    testPair i f ((1+StaticCoefficient.sqrtMultiplier c*StaticCoefficient.sqrtMultiplier c) F) =
      ∫ x : Maxwell.Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
        F (VectorFourier.coordinateMap x) i*f x := by
  rw [testPair_integral]
  change (∫ x : Maxwell.Space, (F+StaticCoefficient.sqrtMultiplier c
    (StaticCoefficient.sqrtMultiplier c F)) (VectorFourier.coordinateMap x) i*f x) = _
  have ha := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add F (StaticCoefficient.sqrtMultiplier c (StaticCoefficient.sqrtMultiplier c F)))
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_square_ae c F)
  apply integral_congr_ae
  filter_upwards [ha,hs] with x ha hs
  rw [ha]
  simp only [Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul]
  change (F (VectorFourier.coordinateMap x) i+
    (c.value (VectorFourier.coordinateMap x) : ℂ)*F (VectorFourier.coordinateMap x) i)*f x = _
  ring

theorem maxwell_test_physical (c : Coefficient) (z : ℂ) (F : VectorL2)
    (i : Fin 3) (f : Test) :
    maxwellTest c z i f F =
      (∑ l : Fin 3, ∫ x : Maxwell.Space, F (VectorFourier.coordinateMap x) l *
        (testPartial l (testPartial i f)).val x) -
      (∑ l : Fin 3, ∫ x : Maxwell.Space, F (VectorFourier.coordinateMap x) i *
        (testPartial l (testPartial l f)).val x) -
      z^2*(∫ x : Maxwell.Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
        F (VectorFourier.coordinateMap x) i*f.val x) := by
  simp only [maxwellTest,curlCurlTest,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul,testPair_integral,
    ←dielectric_test_integral]

theorem physical_direct_source (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : IsUnit (ComplexConvolutionAnalytic.volumeBlock c z S)) (g : VectorL2)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T) :
    let F := (z^2)⁻¹ • Packet06LocalPencil.response c z S T
      (Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z S) g)
    (∑ l : Fin 3, ∫ x : Maxwell.Space, F (VectorFourier.coordinateMap x) l *
      (testPartial l (testPartial i f)).val x) -
    (∑ l : Fin 3, ∫ x : Maxwell.Space, F (VectorFourier.coordinateMap x) i *
      (testPartial l (testPartial l f)).val x) -
    z^2*(∫ x : Maxwell.Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
      F (VectorFourier.coordinateMap x) i*f.val x) =
    ∫ x : Maxwell.Space, (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
      g (VectorFourier.coordinateMap x) i*f.val x := by
  dsimp only
  rw [←maxwell_test_physical,direct_source_green c z hz S T hST hplus hc hu g i f hf,
    testPair_integral]
  apply integral_congr_ae
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c g)
  filter_upwards [hs] with x hs
  rw [hs]
  rfl

end OQ14.Packet06GreenPhysical
#print axioms OQ14.Packet06GreenPhysical.dielectric_test_integral
#print axioms OQ14.Packet06GreenPhysical.maxwell_test_physical
#print axioms OQ14.Packet06GreenPhysical.physical_direct_source
