import ComplexResponseAnalytic
import LocalVolumeResponse

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexResponseTests
open MeasureTheory Metric OQ14.Maxwell OQ14.ComplexKernelResponse
open scoped SchwartzMap InnerProductSpace ComplexConjugate
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def testPair (i : Fin 3) (f : 𝓢(Space, ℂ)) : VectorL2 →L[ℂ] ℂ where
  toFun := fun F => ⟪FourierL2.embed (NewtonL2.conjugate f), NewtonL2.physicalCoordinate F i⟫_ℂ
  map_add' F G := by
    change ⟪_, (DynamicConvolution.component i) (F+G)⟫_ℂ = _
    simp [map_add, inner_add_right, DynamicConvolution.component_apply]
  map_smul' a F := by
    change ⟪_, (DynamicConvolution.component i) (a • F)⟫_ℂ = _
    simp [map_smul, inner_smul_right, DynamicConvolution.component_apply]
  cont := continuous_const.inner (DynamicConvolution.component i).continuous

theorem testPair_integral (i : Fin 3) (f : 𝓢(Space, ℂ)) (F : VectorL2) :
    testPair i f F = ∫ x : Space, F (VectorFourier.coordinateMap x) i * f x := by
  change ⟪FourierL2.embed (NewtonL2.conjugate f), NewtonL2.physicalCoordinate F i⟫_ℂ = _
  rw [← NewtonL2.scalar_pairing_inner]
  apply integral_congr_ae
  filter_upwards [NewtonL2.physicalCoordinate_ae F i] with x hx
  rw [hx]

theorem response_test_differentiable (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (u : VectorL2) (i : Fin 3) (f : 𝓢(Space, ℂ)) :
    Differentiable ℂ (fun z => testPair i f (response c z R u)) :=
  (testPair i f).differentiable.comp (ComplexResponseAnalytic.response_differentiable c R hR u)

theorem real_response_ball (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x : Space => response c (k : ℂ) R u (VectorFourier.coordinateMap x) i)
      =ᵐ[volume.restrict (closedBall 0 R)] fun x => MaterialField.scattered c k u x i := by
  have h := LocalVolumeResponse.electric_ae_on_ball k R R (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (DynamicVolume.source_zero c u R hc) (StaticNewton.material_source_ae c u) i
  have he := ae_restrict_of_ae (s := closedBall (0 : Space) R) (NewtonL2.physicalCoordinate_ae
    (LocalVolumeResponse.localRepresentative k R R (StaticCoefficient.sqrtMultiplier c u)) i)
  filter_upwards [h, he] with x hx hy
  have hr : response c (k : ℂ) R u = LocalVolumeResponse.localRepresentative k R R (StaticCoefficient.sqrtMultiplier c u) := by
    simp only [ComplexResponseAnalytic.response_ofReal, LocalVolumeResponse.localRepresentative, ← two_mul]
  rw [hr, ← hy, hx]
  rfl

#print axioms OQ14.ComplexResponseTests.testPair_integral
#print axioms OQ14.ComplexResponseTests.response_test_differentiable
#print axioms OQ14.ComplexResponseTests.real_response_ball
end OQ14.ComplexResponseTests




