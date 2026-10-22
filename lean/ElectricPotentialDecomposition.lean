import ScalarPotentialBound
import MagneticLocal
import LocalVolumeResponse

/-! The actual Maxwell volume response is a weak scalar gradient plus a
continuous correction of order frequency squared. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ElectricPotentialDecomposition
open MeasureTheory Metric OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

def potential (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) : ℂ :=
  ∑ j : Fin 3, response (fun z => GreenKernel.phiGradient k z j) (ρ j) x

def correction (k : ℝ) (ρ : Fin 3 → Space → ℂ) : Field :=
  fun x i => (k : ℂ)^2*response (GreenKernel.phi k) (ρ i) x

theorem potential_test_integrable (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j)) (f : Test) :
    Integrable (fun x => potential k ρ x*f.val x) := by
  simpa only [potential,Finset.sum_mul] using integrable_finset_sum Finset.univ
    (fun j _ => FieldResponse.response_test_integrable _ _
      (KernelGradient.gradient_locallyIntegrable k j) (hρ j) (hc j) f)

theorem correction_test_integrable (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j)) (i : Fin 3) (f : Test) :
    Integrable (fun x => correction k ρ x i*f.val x) := by
  simpa only [correction,mul_assoc] using
    (FieldResponse.response_test_integrable _ _ (KernelIntegrability.phi_locallyIntegrable k)
      (hρ i) (hc i) f).const_mul ((k : ℂ)^2)

theorem potential_weak_partial (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) (f : Test) :
    (∫ x, potential k ρ x*(testPartial i f).val x)=
      -(∫ x, (FieldResponse.electric k F ρ x i-correction k ρ x i)*f.val x) := by
  have hv : (∫ x, potential k ρ x*(testPartial i f).val x)=
      -(∑ j : Fin 3, MagneticResponse.potentialPair k (ρ j) (testPartial j (testPartial i f))) := by
    simp only [potential,Finset.sum_mul]
    rw [integral_finset_sum _ (fun j _ => FieldResponse.response_test_integrable _ _
      (KernelGradient.gradient_locallyIntegrable k j) (hρ j) (hc j) (testPartial i f))]
    simp only [MagneticResponse.gradient_pairing k _ (hρ _) (hc _),Finset.sum_neg_distrib]
  have hw : (∫ x, correction k ρ x i*f.val x)=
      (k : ℂ)^2*MagneticResponse.potentialPair k (ρ i) f := by
    simp only [correction,mul_assoc,integral_const_mul]
    rw [MagneticResponse.potential_pairing k (ρ i) (hρ i) (hc i) f]
  simp only [sub_mul]
  rw [integral_sub (FieldResponse.electric_test_integrable k F ρ hρ hc i f)
    (correction_test_integrable k ρ hρ hc i f),
    MagneticResponse.electric_potential_pairing k F ρ hρ hc hF i f,hw]
  simpa only [add_sub_cancel_left] using hv

theorem potential_memLp_ball (k R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) :
    MemLp (potential k ρ) 2 (volume.restrict (closedBall 0 R)) := by
  apply memLp_finset_sum
  intro j _
  exact MagneticLocal.gradient_response_memLp_ball k R S F ρ hρ hc hF j j

theorem gradient_memLp_ball (k R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) :
    MemLp (fun x => FieldResponse.electric k F ρ x i-correction k ρ x i) 2
      (volume.restrict (closedBall 0 R)) :=
  (LocalVolumeResponse.electric_memLp_ball k R S F ρ hρ hc hF i).sub
    ((LocalConvolution.response_memLp_ball _ (KernelIntegrability.phi_locallyIntegrable k)
      (ρ i) (hρ i) (NewtonL2.physicalCoordinate F i) (hF i) R S (hc i)).const_mul ((k : ℂ)^2))

theorem correction_continuous (k S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3) :
    Continuous (fun x => correction k ρ x i) :=
  continuous_const.mul (ScalarPotentialBound.response_continuous k S (ρ i)
    (NewtonL2.physicalCoordinate F i) (hF i) (hc i))

theorem correction_bound (k R S : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j) (i : Fin 3)
    (x : Space) (hx : x ∈ closedBall 0 R) :
    ‖correction k ρ x i‖ ≤ k^2*‖NewtonL2.physicalCoordinate F i‖*
      ‖ScalarPotentialBound.cutoff 0 (R+S)‖ :=
  ScalarPotentialBound.scaled_response_bound k R S (ρ i) (NewtonL2.physicalCoordinate F i)
    (hF i) (hc i) x hx

end OQ14.ElectricPotentialDecomposition

#print axioms OQ14.ElectricPotentialDecomposition.potential_test_integrable
#print axioms OQ14.ElectricPotentialDecomposition.correction_test_integrable
#print axioms OQ14.ElectricPotentialDecomposition.potential_weak_partial
#print axioms OQ14.ElectricPotentialDecomposition.potential_memLp_ball
#print axioms OQ14.ElectricPotentialDecomposition.gradient_memLp_ball
#print axioms OQ14.ElectricPotentialDecomposition.correction_continuous
#print axioms OQ14.ElectricPotentialDecomposition.correction_bound
