import Packet06ResponseLinear
import ComplexResponseOverlap
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexElectric
open MeasureTheory Metric OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

def electric (z : ℂ) (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ) : Field :=
  fun x i => NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x +
    ∑ j, response (fun y => ComplexDynamicKernel.remainder z y i j) (ρ j) x

theorem static_pairing (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) (f : Test) :
    (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x * f.val x) =
      ∑ j, Packet06ComplexPotentialPair.potentialPair 0 (ρ j) (testPartial j (testPartial i f)) := by
  have he : FieldResponse.electric 0 F ρ = fun x i => NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x := by
    funext x i
    simp [FieldResponse.electric, KernelConvolution.response, DyadicKernel.remainder, DyadicKernel.dyadic]
  have h := MagneticResponse.electric_potential_pairing 0 F ρ hρ hc hF i f
  rw [he] at h
  simpa [MagneticResponse.potentialPair,
    Packet06ComplexPotentialPair.potentialPair, Packet06ComplexPotentialPair.scalarPair] using h

theorem electric_pairing (z : ℂ) (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) (f : Test) :
    (∫ x, electric z F ρ x i * f.val x) =
      z^2 * Packet06ComplexPotentialPair.potentialPair z (ρ i) f +
        ∑ j, Packet06ComplexPotentialPair.potentialPair z (ρ j) (testPartial j (testPartial i f)) := by
  have hs := NewtonL2.scalar_pairing_integrable (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i) f.val
  have hd (j : Fin 3) := FieldResponse.response_test_integrable _ _
    (ComplexDynamicKernel.remainder_locallyIntegrable z i j) (hρ j) (hc j) f
  simp only [electric, add_mul, Finset.sum_mul]
  rw [integral_add hs (integrable_finset_sum Finset.univ (fun j _ => hd j)),
    integral_finset_sum _ (fun j _ => hd j), static_pairing F ρ hρ hc hF i f]
  simp_rw [Packet06ResponseLinear.dynamic_pairing z _ (hρ _) (hc _) i _ f]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
  simp

theorem potential_weak_partial (z : ℂ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) (f : Test) :
    (∫ x, Packet06ComplexPotential.potential z ρ x * (testPartial i f).val x) =
      -(∫ x, (electric z F ρ x i - Packet06ComplexPotential.correction z ρ x i) * f.val x) := by
  have hi : Integrable (fun x => electric z F ρ x i * f.val x) := by
    have hs := NewtonL2.scalar_pairing_integrable (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i) f.val
    have hd (j : Fin 3) := FieldResponse.response_test_integrable _ _
      (ComplexDynamicKernel.remainder_locallyIntegrable z i j) (hρ j) (hc j) f
    simpa only [electric, add_mul, Finset.sum_mul] using hs.add (integrable_finset_sum Finset.univ (fun j _ => hd j))
  have hw : Integrable (fun x => Packet06ComplexPotential.correction z ρ x i * f.val x) := by
    simpa only [Packet06ComplexPotential.correction, mul_assoc] using
      (FieldResponse.response_test_integrable _ _ (Packet06ComplexScalarKernel.phi_locallyIntegrable z)
        (hρ i) (hc i) f).const_mul (z^2)
  have hp := Packet06ComplexPotentialPair.potential_gradient_test z ρ hρ hc i f
  simp only [sub_mul]
  rw [integral_sub hi hw, electric_pairing z F ρ hρ hc hF i f]
  simp only [Packet06ComplexPotential.correction, mul_assoc, integral_const_mul]
  rw [Packet06ComplexPotentialPair.potential_pairing z (ρ i) (hρ i) (hc i) f]
  simpa using hp

theorem electric_ae_on_ball (z : ℂ) (S T : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) :
    (fun x => (NewtonL2.newtonOperator F + ComplexConvolutionAnalytic.operator z (T+S) F)
      (VectorFourier.coordinateMap x) i) =ᵐ[volume.restrict (closedBall 0 T)] (fun x => electric z F ρ x i) := by
  have hd := ComplexResponseOverlap.dynamic_ae_on_ball z S T F ρ hρ hc hF i
  have ha := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (NewtonL2.newtonOperator F) (ComplexConvolutionAnalytic.operator z (T+S) F))
  have hn := NewtonL2.physicalCoordinate_ae (NewtonL2.newtonOperator F) i
  filter_upwards [hd, ae_restrict_of_ae ha, ae_restrict_of_ae hn] with x hd' ha' hn'
  change (NewtonL2.newtonOperator F + ComplexConvolutionAnalytic.operator z (T+S) F)
    (VectorFourier.coordinateMap x) i = _
  rw [ha']
  change NewtonL2.newtonOperator F (VectorFourier.coordinateMap x) i +
    ComplexConvolutionAnalytic.operator z (T+S) F (VectorFourier.coordinateMap x) i = _
  rw [hd', ← hn']
  simp only [electric, KernelConvolution.response]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem electric_memLp_ball (z : ℂ) (R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) :
    MemLp (fun x => electric z F ρ x i) 2 (volume.restrict (closedBall 0 R)) := by
  let V := NewtonL2.newtonOperator F + ComplexConvolutionAnalytic.operator z (R+S) F
  have hrep := NewtonL2.physicalCoordinate_ae V i
  have hmatch := electric_ae_on_ball z S R F ρ hρ hc hF i
  have he : (fun x => NewtonL2.physicalCoordinate V i x) =ᵐ[volume.restrict (closedBall 0 R)]
      fun x => electric z F ρ x i := by
    filter_upwards [ae_restrict_of_ae hrep,hmatch] with x hx hy
    exact hx.trans hy
  exact ((Lp.memLp (NewtonL2.physicalCoordinate V i)).restrict (closedBall 0 R)).ae_eq he

#print axioms OQ14.Packet06ComplexElectric.static_pairing
#print axioms OQ14.Packet06ComplexElectric.electric_pairing
#print axioms OQ14.Packet06ComplexElectric.potential_weak_partial
#print axioms OQ14.Packet06ComplexElectric.electric_ae_on_ball
#print axioms OQ14.Packet06ComplexElectric.electric_memLp_ball
end OQ14.Packet06ComplexElectric
