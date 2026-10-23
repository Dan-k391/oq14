import RadiatingTrace

/-! The actual compact electric-source response and cancellation of equal Maxwell sources. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ForcedMaxwellResponse
open MeasureTheory Filter OQ14.Maxwell OQ14.MaterialMaxwell OQ14.MagneticResponse

def TestForced (k : ℝ) (ρ : Fin 3 → Space → ℂ) (E H : Field) : Prop :=
  ∀ (i : Fin 3) (f : DynamicSource.Test),
    curlPair (fieldPair E) i f=Complex.I*(k : ℂ)*fieldPair H i f ∧
    curlPair (fieldPair H) i f= -(Complex.I*(k : ℂ))*(fieldPair E i f+∫ x,ρ i x*f.val x)

theorem fieldPair_sub (E E' : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hE' : ∀ i, LocallyIntegrable (fun x => E' x i)) (i : Fin 3) (f : DynamicSource.Test) :
    fieldPair (E-E') i f=fieldPair E i f-fieldPair E' i f := by
  simp only [fieldPair,Pi.sub_apply,sub_mul]
  exact integral_sub
    (PointSingularity.test_product_integrable _ _ (hE i) f.val.continuous f.property)
    (PointSingularity.test_product_integrable _ _ (hE' i) f.val.continuous f.property)

theorem curlPair_sub (A B : Fin 3 → DynamicSource.Test → ℂ) (i : Fin 3) (f : DynamicSource.Test) :
    curlPair (fun j g => A j g-B j g) i f=curlPair A i f-curlPair B i f := by
  unfold curlPair
  ring

theorem forced_congr (k : ℝ) (ρ : Fin 3 → Space → ℂ) (E H E' H' : Field)
    (hE : E =ᵐ[volume] E') (hH : H =ᵐ[volume] H') (h : TestForced k ρ E H) :
    TestForced k ρ E' H' := by
  have he := ExteriorMaterial.fieldPair_congr E E' hE
  have hh := ExteriorMaterial.fieldPair_congr H H' hH
  simpa only [TestForced,he,hh] using h

theorem difference_vacuum (k : ℝ) (ρ : Fin 3 → Space → ℂ) (E H E' H' : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hE' : ∀ i, LocallyIntegrable (fun x => E' x i))
    (hH' : ∀ i, LocallyIntegrable (fun x => H' x i))
    (h : TestForced k ρ E H) (h' : TestForced k ρ E' H') :
    TestMaxwell k (fun _ => 1) (E-E') (H-H') := by
  have ep : fieldPair (E-E')=fun i f => fieldPair E i f-fieldPair E' i f :=
    funext (fun i => funext (fun f => fieldPair_sub E E' hE hE' i f))
  have hp : fieldPair (H-H')=fun i f => fieldPair H i f-fieldPair H' i f :=
    funext (fun i => funext (fun f => fieldPair_sub H H' hH hH' i f))
  intro i f
  constructor
  · rw [ep,hp,curlPair_sub,(h i f).1,(h' i f).1]
    ring
  · simp only [Complex.ofReal_one,one_mul]
    change curlPair (fieldPair (H-H')) i f= -(Complex.I*(k : ℂ))*fieldPair (E-E') i f
    rw [ep,hp,curlPair_sub,(h i f).2,(h' i f).2]
    ring

theorem response_forced (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j) :
    TestForced k ρ (FieldResponse.electric k F ρ) (magnetic k ρ) :=
  fun i f => ⟨electric_curl_pairing k F ρ hρ hc hF i f,magnetic_curl_pairing k F ρ hρ hc hF i f⟩

theorem representative_forced (k R : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j) :
    TestForced k ρ (ExteriorContinuity.representative k F ρ R) (magnetic k ρ) :=
  forced_congr k ρ _ _ _ _ (ExteriorContinuity.representative_ae k F ρ hρ hF R hs).symm
    EventuallyEq.rfl (response_forced k F ρ hρ
      (fun j => NewtonExteriorResponse.source_compact (ρ j) R (hs j)) hF)

end OQ14.ForcedMaxwellResponse
#print axioms OQ14.ForcedMaxwellResponse.fieldPair_sub
#print axioms OQ14.ForcedMaxwellResponse.curlPair_sub
#print axioms OQ14.ForcedMaxwellResponse.forced_congr
#print axioms OQ14.ForcedMaxwellResponse.difference_vacuum
#print axioms OQ14.ForcedMaxwellResponse.response_forced
#print axioms OQ14.ForcedMaxwellResponse.representative_forced
