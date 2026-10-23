import RestrictedTEMagneticTail
import TransversePlaneFlux

/-! Genuine inverse-cube coherent tails for the actual finite restricted TE inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTECoherentTail
open Complex Filter Set Metric MeasureTheory Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space

theorem dynamic_tail (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ K : ℝ, 0≤K ∧ ∃ T : ℝ, 2≤T ∧ 2*R≤T ∧ ∀ (d : ℝ) (S : Source), Admissible R d S →
      ∀ q : Plane, T<‖q‖ → ‖dynamicMixed S A q‖≤K*sourceMass S/‖q‖^3 := by
  obtain ⟨C,hC,T,hT,hb⟩ := RestrictedTEMagneticTail.field_bounds A
  let K := 2*C*(MaxwellPlaneTail.electricErrorConstant 1 R+MaxwellPlaneTail.leadingConstant 1)
  have hE : 0≤MaxwellPlaneTail.electricErrorConstant 1 R := by unfold MaxwellPlaneTail.electricErrorConstant; positivity
  have hL : 0≤MaxwellPlaneTail.leadingConstant 1 := by unfold MaxwellPlaneTail.leadingConstant; positivity
  refine ⟨K,by dsimp [K]; positivity,max T (2*R),hT.trans (le_max_left _ _),le_max_right _ _,?_⟩
  intro d S hS q hq
  let x := MaxwellPlaneTail.planePoint q
  have hxn : ‖x‖=‖q‖ := MaxwellPlaneTail.planePoint_norm q
  have hxT : T<‖x‖ := by rw [hxn]; exact lt_of_le_of_lt (le_max_left _ _) hq
  have hxR : 2*R<‖x‖ := by rw [hxn]; exact lt_of_le_of_lt (le_max_right _ _) hq
  have hx2 : 2≤‖x‖ := hT.trans hxT.le
  have hxpos : 0<‖x‖ := by linarith
  have hx0 : x≠0 := norm_pos_iff.mp hxpos
  have hmass := sourceMass_nonnegative S
  have hs := hb x hxT
  have herr : ∀ i, ‖magnetic A x i-TransversePlaneFlux.tangentPart x (magnetic A x) i‖≤C/‖x‖^2 :=
    TransversePlaneFlux.radial_error_bound x hx0 (magnetic A x) _ (by positivity) hs.2
  have h := MaxwellPlaneTail.cross_perturbation_bound
    (ExteriorContinuity.electric 1 S x) (magnetic A x)
    (leadingElectric 1 S x) (TransversePlaneFlux.tangentPart x (magnetic A x))
    (MaxwellPlaneTail.leadingConstant 1*sourceMass S/‖x‖) (C/‖x‖)
    (MaxwellPlaneTail.electricErrorConstant 1 R*sourceMass S/‖x‖^2) (C/‖x‖^2)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (MaxwellPlaneTail.leading_electric_bound 1 R hR S hS.integrable hS.support x hxR)
    hs.1 (MaxwellPlaneTail.electric_error_bound 1 R hR S hS.integrable hS.support x hxR hx2)
    herr (TransversePlaneFlux.leading_zero 1 S x hx0 (by rfl) (magnetic A x))
  change ‖dynamicMixed S A q‖≤_ at h
  exact h.trans_eq (by rw [hxn]; dsimp [K]; field_simp; ring)

theorem error_tail (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ K : ℝ, 0≤K ∧ ∃ T : ℝ, 2≤T ∧ 2*R≤T ∧ ∀ (d : ℝ), 0<d →
      ∀ (S : Source), Admissible R d S → ∀ q : Plane, T<‖q‖ →
        ‖coherentError S A q‖≤K*sourceMass S/‖q‖^3 := by
  obtain ⟨K,hK,T,hT,hTR,hb⟩ := dynamic_tail A R hR
  obtain ⟨B,hB,hH⟩ := RestrictedTEMagnetic.magnetic_bounded A
  refine ⟨K+(16/Real.pi)*B,by positivity,T,hT,hTR,?_⟩
  intro d hd S hS q hq
  have hs := StaticSourceTail.field_bound R d hR hd S hS q (lt_of_le_of_lt hTR hq)
  have hmass := sourceMass_nonnegative S
  have hbound := MaxwellPlaneTail.cross_norm_bound
    (NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q))
    (magnetic A (MaxwellPlaneTail.planePoint q)) (((8/Real.pi)/‖q‖^3)*sourceMass S) B
    (by positivity) hB hs (hH _) 2
  have he : ‖staticMixed S A q‖≤(16/Real.pi)*B*sourceMass S/‖q‖^3 :=
    hbound.trans_eq (by ring)
  exact ((norm_sub_le _ _).trans (add_le_add (hb d S hS q hq) he)).trans_eq (by ring)

theorem whole_error_mass (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ W : ℝ, 0≤W ∧ ∃ T : ℝ, 2≤T ∧ 2*R≤T ∧ ∀ (d : ℝ), 0<d → d≤T+R →
      ∀ (S : Source), Admissible R d S → Integrable (coherentError S A) ∧
        (∫ q : Plane, ‖coherentError S A q‖)≤W*sourceMass S := by
  obtain ⟨K,hK,T,hT,hTR,hb⟩ := error_tail A R hR
  obtain ⟨B,hB,hl⟩ := local_error_mass A
  let W := 2*B*PlaneMaxwellSharp.remainderMass 1 R T+K*PlaneInverseCube.diskConstant/T
  have hTpos : 0<T := by linarith
  have hrem : 0≤PlaneMaxwellSharp.remainderMass 1 R T := by unfold PlaneMaxwellSharp.remainderMass; positivity
  have hdisk : 0≤PlaneInverseCube.diskConstant := by unfold PlaneInverseCube.diskConstant; positivity
  refine ⟨W,by dsimp [W]; positivity,T,hT,hTR,?_⟩
  intro d hd hdM S hS
  have hl := hl R T d hd hdM S hS
  have hc := error_continuous R d hd S hS A
  have ht := PlaneInverseCube.tail_integrable T (K*sourceMass S) hTpos hc.aestronglyMeasurable.restrict
    (hb d hd S hS)
  have hu := PlaneInverseCube.tail_integral_bound T (K*sourceMass S) hTpos hc.aestronglyMeasurable.restrict
    (hb d hd S hS)
  have he : {q : Plane | T<‖q‖}=(closedBall (0 : Plane) T)ᶜ := by
    ext q
    simp [mem_closedBall,dist_zero_right,not_le]
  rw [he] at ht hu
  have hi : Integrable (coherentError S A) := by
    simpa only [union_compl_self,integrableOn_univ] using hl.1.union ht
  refine ⟨hi,?_⟩
  rw [← integral_add_compl isClosed_closedBall.measurableSet hi.norm]
  exact (add_le_add hl.2 hu).trans_eq (by dsimp [W]; ring)

end OQ14.RestrictedTECoherentTail
#print axioms OQ14.RestrictedTECoherentTail.dynamic_tail
#print axioms OQ14.RestrictedTECoherentTail.error_tail
#print axioms OQ14.RestrictedTECoherentTail.whole_error_mass
