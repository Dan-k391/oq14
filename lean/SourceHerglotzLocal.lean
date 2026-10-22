import PlaneMaxwellFields
import SphereMagneticKernel

/-! Actual local coherent pairings of a volume response with a point Herglotz column. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceHerglotzLocal
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open SphereReactionKernel (J J_bound J_continuous entryBound entryBound_nonnegative)
open SphereMagneticKernel (K K_bound K_continuous)
open Maxwell (conjugate)
open scoped ComplexConjugate Topology
abbrev Space := FourierL2.Space

def electricFlux (k : ℝ) (ρ : Source) (z : Space) (m : Fin 3) (q : Plane) : ℂ :=
  crossProduct (ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q))
    (conjugate (fun i => K k (MaxwellPlaneTail.planePoint q-z) i m)) 2

def magneticFlux (k : ℝ) (ρ : Source) (z : Space) (j : Fin 3) (q : Plane) : ℂ :=
  crossProduct (fun i => J k (MaxwellPlaneTail.planePoint q-z) i j)
    (conjugate (MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q))) 2

theorem electric_continuous (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (z : Space) (m : Fin 3) : Continuous (electricFlux k ρ z m) := by
  have hK (i : Fin 3) : Continuous (fun q : Plane => K k (MaxwellPlaneTail.planePoint q-z) i m) :=
    (K_continuous k i m).comp (MaxwellPlaneTail.planePoint_continuous.sub continuous_const)
  exact ((electric_plane_continuous k R d hd ρ hρ 0).mul (hK 1).star).sub
    ((electric_plane_continuous k R d hd ρ hρ 1).mul (hK 0).star)

theorem magnetic_continuous (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (z : Space) (j : Fin 3) : Continuous (magneticFlux k ρ z j) := by
  have hJ (i : Fin 3) : Continuous (fun q : Plane => J k (MaxwellPlaneTail.planePoint q-z) i j) :=
    (J_continuous k i j).comp (MaxwellPlaneTail.planePoint_continuous.sub continuous_const)
  exact ((hJ 0).mul (magnetic_plane_continuous k R d hd ρ hρ 1).star).sub
    ((hJ 1).mul (magnetic_plane_continuous k R d hd ρ hρ 0).star)

theorem electric_local_mass (k R T d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (z : Space) (m : Fin 3) :
    IntegrableOn (electricFlux k ρ z m) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖electricFlux k ρ z m q‖) ≤
      (2*entryBound k*(PlaneMaxwellLocal.electricCoefficient k R T*
        ((Real.pi+PlaneInverseCube.diskConstant)/d)))*sourceMass ρ := by
  let E := fun q i => ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q) i
  have he (i : Fin 3) := PlaneMaxwellFields.electric_mass k R T d hd ρ hρ i
  have hb (q : Plane) : ‖electricFlux k ρ z m q‖ ≤ entryBound k*(‖E q 0‖+‖E q 1‖) := by
    change ‖E q 0*star (K k (MaxwellPlaneTail.planePoint q-z) 1 m)-
      E q 1*star (K k (MaxwellPlaneTail.planePoint q-z) 0 m)‖ ≤ _
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, norm_star]
    exact (add_le_add (mul_le_mul_of_nonneg_left (K_bound k _ 1 m) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (K_bound k _ 0 m) (norm_nonneg _))).trans_eq (by ring)
  have hg : IntegrableOn (fun q => entryBound k*(‖E q 0‖+‖E q 1‖)) (closedBall 0 T) :=
    ((he 0).1.norm.add (he 1).1.norm).const_mul _
  have hi := hg.mono' (electric_continuous k R d hd ρ hρ z m).aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, entryBound k*(‖E q 0‖+‖E q 1‖) :=
      integral_mono_ae hi.norm hg (Filter.Eventually.of_forall hb)
    _ = entryBound k*((∫ q : Plane in closedBall 0 T, ‖E q 0‖)+
        (∫ q : Plane in closedBall 0 T, ‖E q 1‖)) := by
      rw [integral_const_mul, integral_add (he 0).1.norm (he 1).1.norm]
    _ ≤ entryBound k*((PlaneMaxwellLocal.electricCoefficient k R T*
        ((Real.pi+PlaneInverseCube.diskConstant)/d))*sourceMass ρ+
        (PlaneMaxwellLocal.electricCoefficient k R T*((Real.pi+PlaneInverseCube.diskConstant)/d))*sourceMass ρ) :=
      mul_le_mul_of_nonneg_left (add_le_add (he 0).2 (he 1).2) (entryBound_nonnegative k)
    _ = _ := by ring

theorem magnetic_local_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R) (ρ : Source)
    (hρ : Admissible R d ρ) (z : Space) (j : Fin 3) :
    IntegrableOn (magneticFlux k ρ z j) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖magneticFlux k ρ z j q‖) ≤
      (4*entryBound k*|k| * PlaneMaxwellSharp.gradientMass k R T d)*sourceMass ρ := by
  let H := fun q i => MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) i
  have hh (i : Fin 3) := PlaneMaxwellFields.magnetic_mass k R T d hd hdM ρ hρ i
  have hb (q : Plane) : ‖magneticFlux k ρ z j q‖ ≤ entryBound k*(‖H q 0‖+‖H q 1‖) := by
    change ‖J k (MaxwellPlaneTail.planePoint q-z) 0 j*star (H q 1)-
      J k (MaxwellPlaneTail.planePoint q-z) 1 j*star (H q 0)‖ ≤ _
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, norm_star]
    exact (add_le_add (mul_le_mul_of_nonneg_right (J_bound k _ 0 j) (norm_nonneg _))
      (mul_le_mul_of_nonneg_right (J_bound k _ 1 j) (norm_nonneg _))).trans_eq (by ring)
  have hg : IntegrableOn (fun q => entryBound k*(‖H q 0‖+‖H q 1‖)) (closedBall 0 T) :=
    ((hh 0).1.norm.add (hh 1).1.norm).const_mul _
  have hi := hg.mono' (magnetic_continuous k R d hd ρ hρ z j).aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall hb)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, entryBound k*(‖H q 0‖+‖H q 1‖) :=
      integral_mono_ae hi.norm hg (Filter.Eventually.of_forall hb)
    _ = entryBound k*((∫ q : Plane in closedBall 0 T, ‖H q 0‖)+
        (∫ q : Plane in closedBall 0 T, ‖H q 1‖)) := by
      rw [integral_const_mul, integral_add (hh 0).1.norm (hh 1).1.norm]
    _ ≤ entryBound k*((2 * |k| * PlaneMaxwellSharp.gradientMass k R T d)*sourceMass ρ+
        (2 * |k| * PlaneMaxwellSharp.gradientMass k R T d)*sourceMass ρ) :=
      mul_le_mul_of_nonneg_left (add_le_add (hh 0).2 (hh 1).2) (entryBound_nonnegative k)
    _ = _ := by ring

theorem electric_sub_mass (k R T d : ℝ) (hd : 0 < d) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) (z : Space) (m : Fin 3) :
    IntegrableOn (fun q => electricFlux k ρ z m q-electricFlux k σ z m q) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖electricFlux k ρ z m q-electricFlux k σ z m q‖) ≤
      (2*entryBound k*(PlaneMaxwellLocal.electricCoefficient k R T*
        ((Real.pi+PlaneInverseCube.diskConstant)/d)))*sourceMass (ρ-σ) := by
  have he (q : Plane) : electricFlux k (ρ-σ) z m q=electricFlux k ρ z m q-electricFlux k σ z m q := by
    unfold electricFlux
    rw [electric_plane_sub k R d hd ρ σ hρ hσ q]
    simp [cross_apply, conjugate]
  have hefun := funext he
  simpa only [he, hefun] using electric_local_mass k R T d hd (ρ-σ) (admissible_sub R d ρ σ hρ hσ) z m

theorem magnetic_sub_mass (k R T d : ℝ) (hd : 0 < d) (hdM : d ≤ T+R) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) (z : Space) (j : Fin 3) :
    IntegrableOn (fun q => magneticFlux k ρ z j q-magneticFlux k σ z j q) (closedBall 0 T) ∧
    (∫ q : Plane in closedBall 0 T, ‖magneticFlux k ρ z j q-magneticFlux k σ z j q‖) ≤
      (4*entryBound k*|k| * PlaneMaxwellSharp.gradientMass k R T d)*sourceMass (ρ-σ) := by
  have he (q : Plane) : magneticFlux k (ρ-σ) z j q=magneticFlux k ρ z j q-magneticFlux k σ z j q := by
    unfold magneticFlux
    rw [magnetic_plane_sub k R d hd ρ σ hρ hσ q]
    simp [cross_apply, conjugate]
    all_goals ring
  have hefun := funext he
  simpa only [he, hefun] using magnetic_local_mass k R T d hd hdM (ρ-σ) (admissible_sub R d ρ σ hρ hσ) z j
end OQ14.SourceHerglotzLocal
#print axioms OQ14.SourceHerglotzLocal.electric_continuous
#print axioms OQ14.SourceHerglotzLocal.magnetic_continuous
#print axioms OQ14.SourceHerglotzLocal.electric_local_mass
#print axioms OQ14.SourceHerglotzLocal.magnetic_local_mass

#print axioms OQ14.SourceHerglotzLocal.electric_sub_mass
#print axioms OQ14.SourceHerglotzLocal.magnetic_sub_mass
