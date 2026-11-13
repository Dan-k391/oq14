import Packet06ComplexPotential
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexPotentialPair
open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

def scalarPair (z : ℂ) (f : Test) : ℂ := ∫ x, ComplexGreenKernel.phi z x * f.val x
def potentialPair (z : ℂ) (ρ : Space → ℂ) (f : Test) : ℂ :=
  ∫ y, ρ y * scalarPair z (translate y f)

theorem potential_pairing (z : ℂ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : Test) :
    (∫ x, response (ComplexGreenKernel.phi z) ρ x * f.val x) = potentialPair z ρ f := by
  rw [response_pairing _ ρ (Packet06ComplexScalarKernel.phi_locallyIntegrable z) hρ hc f]
  simp only [potentialPair, scalarPair, translated_pairing]

theorem gradient_pairing (z : ℂ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i : Fin 3) (f : Test) :
    (∫ x, response (fun y => ComplexGreenKernel.phiGradient z y i) ρ x * f.val x) =
      -potentialPair z ρ (testPartial i f) := by
  rw [response_pairing _ ρ (ComplexMagneticLocal.gradient_locallyIntegrable z i) hρ hc f]
  unfold potentialPair
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  rw [← translated_pairing (fun x => ComplexGreenKernel.phiGradient z x i) y f]
  rw [Packet06ComplexPotential.phi_weak_partial z i (translate y f).val
    ((translate y f).val.smooth 1) (translate y f).property]
  rw [translate_partial]
  simp only [scalarPair, testPartial, GradientProjection.pderivative_apply, mul_neg]

theorem potential_gradient_test (z : ℂ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j)) (i : Fin 3) (f : Test) :
    (∫ x, Packet06ComplexPotential.potential z ρ x * (testPartial i f).val x) =
      -(∑ j : Fin 3, potentialPair z (ρ j) (testPartial j (testPartial i f))) := by
  simp only [Packet06ComplexPotential.potential,Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ => FieldResponse.response_test_integrable _ _
    (ComplexMagneticLocal.gradient_locallyIntegrable z j) (hρ j) (hc j) (testPartial i f))]
  simp only [gradient_pairing z _ (hρ _) (hc _),Finset.sum_neg_distrib]
#print axioms OQ14.Packet06ComplexPotentialPair.potential_pairing
#print axioms OQ14.Packet06ComplexPotentialPair.gradient_pairing
#print axioms OQ14.Packet06ComplexPotentialPair.potential_gradient_test
end OQ14.Packet06ComplexPotentialPair
