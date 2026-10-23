import BoundedMaxwellWeak
import ParityMaterialMaxwell

/-! Actual finite parity illumination and its literal material inverse satisfy weak Maxwell equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteParityWeak
open MeasureTheory Maxwell MaterialMaxwell FiniteHerglotzFlux
open SphereReactionKernel (entryBound)
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem magnetic_derivative_bound (k : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (x : Space) (i : Fin 3) :
    ‖fderiv ℝ (fun z => magnetic k e p j A z i) x‖ ≤ (3*entryBound k*|k|)*(∑ s, ‖A s‖) := by
  classical
  unfold magnetic
  rw [fderiv_sum (fun s _ => (SphereParityMaxwell.magnetic_differentiable (e s) k x (p s) i (j s)).const_mul (A s))]
  calc
    _ ≤ ∑ s, ‖fderiv ℝ (fun z => A s*SphereMagneticParity.magneticReaction (e s) k z (p s) i (j s)) x‖ := norm_sum_le _ _
    _ ≤ ∑ s, ‖A s‖*(3*entryBound k*|k|) := Finset.sum_le_sum (fun s _ => by
      rw [fderiv_const_mul (SphereParityMaxwell.magnetic_differentiable (e s) k x (p s) i (j s))]
      exact ((fderiv ℝ (fun z => SphereMagneticParity.magneticReaction (e s) k z (p s) i (j s)) x).opNorm_smul_le (A s)).trans
        (mul_le_mul_of_nonneg_left (SphereParityDifferential.magnetic_differential_bound (e s) k x (p s) i (j s)) (norm_nonneg _)))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem testMaxwell (k : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) :
    TestMaxwell k (fun _ => 1) (electric k e p j A) (magnetic k e p j A) :=
  BoundedMaxwellWeak.testMaxwell k _ _
    (fun x i => FiniteSphereMaxwell.electric_differentiable k e p j A x i)
    (fun x i => FiniteSphereMaxwell.magnetic_differentiable k e p j A x i)
    _ _ (fun x i => FiniteSphereIncident.electric_derivative_bound k e p j A x i)
    (fun x i => magnetic_derivative_bound k e p j A x i) (fun x => FiniteSphereMaxwell.maxwell k e p j A x)

theorem material_inverse (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (k B : ℝ) (hsmall : ParityReactionVolume.perturbationBound d k B < 1)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) :
    let f := FiniteSphereIncident.datum c k d.radius e p j A d.ballZero
    TestMaxwell k (dielectric c) (ParityMaterialField.total c k B (ParityMaterialField.solution d k B f) (electric k e p j A))
      (ParityMaterialMaxwell.magnetic c k B (ParityMaterialField.solution d k B f) (magnetic k e p j A)) := by
  apply ParityMaterialMaxwell.inverse_testMaxwell c d k B hsmall _ _ _
    (FiniteSphereIncident.datum_actual c k d.radius e p j A d.ballZero)
  · intro i
    exact (continuous_iff_continuousAt.mpr (fun x => (FiniteSphereMaxwell.electric_differentiable k e p j A x i).continuousAt)).locallyIntegrable
  · intro i
    exact (continuous_iff_continuousAt.mpr (fun x => (FiniteSphereMaxwell.magnetic_differentiable k e p j A x i).continuousAt)).locallyIntegrable
  · exact testMaxwell k e p j A

end OQ14.FiniteParityWeak
#print axioms OQ14.FiniteParityWeak.magnetic_derivative_bound
#print axioms OQ14.FiniteParityWeak.testMaxwell
#print axioms OQ14.FiniteParityWeak.material_inverse
