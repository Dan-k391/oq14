import RestrictedTEMagnetic
import RestrictedTEParity
import StaticCoherentRemainder
import MaxwellPlaneL1

/-! Actual harmonic TE plane geometry and gap-uniform local coherent remainder. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEPlaneLocal
open Complex MeasureTheory Metric Set Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEFields
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space

def electric (A : Index →₀ ℂ) : Field := DebyeMaxwell.teElectric (potential 1 A)
def magnetic (A : Index →₀ ℂ) : Field := DebyeMaxwell.teMagnetic 1 (potential 1 A)

theorem electric_tangent_zero (A : Index →₀ ℂ) (q : Plane) (i : Fin 3) (hi : i≠2) :
    electric A (MaxwellPlaneTail.planePoint q) i=0 := by
  have h := RestrictedTEParity.electric_wall 1 A (MaxwellPlaneTail.planePoint q) i
  rw [SphereMagneticParity.reflect_plane _ (by rfl)] at h
  simp only [SphereReactionKernel.sign,if_neg hi,Complex.ofReal_one,neg_mul,one_mul] at h
  change DebyeMaxwell.teElectric (potential 1 A) (MaxwellPlaneTail.planePoint q) i=0
  linear_combination (1/2 : ℂ)*h

theorem magnetic_normal_zero (A : Index →₀ ℂ) (q : Plane) :
    magnetic A (MaxwellPlaneTail.planePoint q) 2=0 := by
  have h := RestrictedTEParity.magnetic_wall 1 A (MaxwellPlaneTail.planePoint q) 2
  rw [SphereMagneticParity.reflect_plane _ (by rfl)] at h
  norm_num [SphereReactionKernel.sign] at h
  change DebyeMaxwell.teMagnetic 1 (potential 1 A) (MaxwellPlaneTail.planePoint q) 2=0
  linear_combination (1/2 : ℂ)*h

def dynamicMixed (S : Source) (A : Index →₀ ℂ) (q : Plane) : ℂ :=
  crossProduct (ExteriorContinuity.electric 1 S (MaxwellPlaneTail.planePoint q))
    (conjugate (magnetic A (MaxwellPlaneTail.planePoint q))) 2

def staticMixed (S : Source) (A : Index →₀ ℂ) (q : Plane) : ℂ :=
  crossProduct (NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q))
    (conjugate (magnetic A (MaxwellPlaneTail.planePoint q))) 2

def coherentError (S : Source) (A : Index →₀ ℂ) (q : Plane) : ℂ := dynamicMixed S A q-staticMixed S A q

def freeFlux (S : Source) (A : Index →₀ ℂ) (q : Plane) : ℂ :=
  crossProduct (electric A (MaxwellPlaneTail.planePoint q)+ExteriorContinuity.electric 1 S (MaxwellPlaneTail.planePoint q))
    (conjugate (magnetic A (MaxwellPlaneTail.planePoint q)+MagneticResponse.magnetic 1 S (MaxwellPlaneTail.planePoint q))) 2

theorem free_identity (S : Source) (A : Index →₀ ℂ) (q : Plane) :
    freeFlux S A q=dynamicMixed S A q+MaxwellPlaneL1.flux 1 S S q := by
  unfold freeFlux dynamicMixed MaxwellPlaneL1.flux MaxwellPlaneTail.bilinearFlux
  simp [cross_apply,conjugate]
  rw [electric_tangent_zero A q 0 (by decide),electric_tangent_zero A q 1 (by decide)]
  ring

theorem error_remainder (R d : ℝ) (hd : 0<d) (S : Source) (hS : Admissible R d S)
    (A : Index →₀ ℂ) (q : Plane) :
    coherentError S A q=crossProduct
      (fun i => ∑ j, KernelConvolution.response (fun w => DyadicKernel.remainder 1 w i j) (S j) (MaxwellPlaneTail.planePoint q))
      (conjugate (magnetic A (MaxwellPlaneTail.planePoint q))) 2 := by
  simp only [← StaticCoherentRemainder.field_split 1 R d hd S hS]
  simp [coherentError,dynamicMixed,staticMixed,cross_apply,conjugate]
  ring

theorem error_continuous (R d : ℝ) (hd : 0<d) (S : Source) (hS : Admissible R d S)
    (A : Index →₀ ℂ) : Continuous (coherentError S A) := by
  have hs (i : Fin 3) : Continuous (fun q : Plane => NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q) i) := by
    apply continuous_finset_sum
    intro j _
    exact response_plane_continuous _ (StaticPlaneKernel.hessian_measurable i j)
      (fun z hz => NewtonExterior.hessian_continuousAt 0 i j z hz) R d hd S hS j
  have hH (i : Fin 3) : Continuous (fun q : Plane => magnetic A (MaxwellPlaneTail.planePoint q) i) :=
    (RestrictedTEMagnetic.magnetic_continuous A i).comp MaxwellPlaneTail.planePoint_continuous
  exact (((electric_plane_continuous 1 R d hd S hS 0).mul (hH 1).star).sub
    ((electric_plane_continuous 1 R d hd S hS 1).mul (hH 0).star)).sub
    (((hs 0).mul (hH 1).star).sub ((hs 1).mul (hH 0).star))

theorem local_error_mass (A : Index →₀ ℂ) :
    ∃ B : ℝ, 0≤B ∧ ∀ (R T d : ℝ), 0<d → d≤T+R → ∀ (S : Source), Admissible R d S →
      IntegrableOn (coherentError S A) (closedBall 0 T) ∧
      (∫ q : Plane in closedBall 0 T, ‖coherentError S A q‖)≤
        (2*B*PlaneMaxwellSharp.remainderMass 1 R T)*sourceMass S := by
  obtain ⟨B,hB,hbound⟩ := RestrictedTEMagnetic.magnetic_bounded A
  refine ⟨B,hB,?_⟩
  intro R T d hd hdM S hS
  let F := fun q i => ∑ j, KernelConvolution.response (fun w => DyadicKernel.remainder 1 w i j) (S j) (MaxwellPlaneTail.planePoint q)
  have hf (i : Fin 3) := PlaneMaxwellFields.remainder_mass 1 R T d hd hdM S hS i
  have hb (q : Plane) : ‖coherentError S A q‖≤B*(‖F q 0‖+‖F q 1‖) := by
    rw [error_remainder R d hd S hS]
    change ‖F q 0*star (magnetic A (MaxwellPlaneTail.planePoint q) 1)-
      F q 1*star (magnetic A (MaxwellPlaneTail.planePoint q) 0)‖≤_
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_star]
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (hbound _ 1) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hbound _ 0) (norm_nonneg _))).trans_eq (by ring)
  have hg : IntegrableOn (fun q => B*(‖F q 0‖+‖F q 1‖)) (closedBall 0 T) :=
    ((hf 0).1.norm.add (hf 1).1.norm).const_mul _
  have hi := hg.mono' (error_continuous R d hd S hS A).aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall hb)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, B*(‖F q 0‖+‖F q 1‖) :=
      integral_mono_ae hi.norm hg (Filter.Eventually.of_forall hb)
    _ = B*((∫ q : Plane in closedBall 0 T, ‖F q 0‖)+(∫ q : Plane in closedBall 0 T, ‖F q 1‖)) := by
      rw [integral_const_mul,integral_add (hf 0).1.norm (hf 1).1.norm]
    _ ≤ B*(PlaneMaxwellSharp.remainderMass 1 R T*sourceMass S+PlaneMaxwellSharp.remainderMass 1 R T*sourceMass S) :=
      mul_le_mul_of_nonneg_left (add_le_add (hf 0).2 (hf 1).2) hB
    _ = _ := by ring

end OQ14.RestrictedTEPlaneLocal
#print axioms OQ14.RestrictedTEPlaneLocal.electric_tangent_zero
#print axioms OQ14.RestrictedTEPlaneLocal.magnetic_normal_zero
#print axioms OQ14.RestrictedTEPlaneLocal.free_identity
#print axioms OQ14.RestrictedTEPlaneLocal.error_remainder
#print axioms OQ14.RestrictedTEPlaneLocal.error_continuous
#print axioms OQ14.RestrictedTEPlaneLocal.local_error_mass
