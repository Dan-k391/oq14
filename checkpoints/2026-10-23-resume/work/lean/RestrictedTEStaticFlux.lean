import RestrictedTECoherentTail
import RestrictedTEScale
import StaticPlaneSource

/-! Actual whole-plane static coherent fields and dynamic flux integrability for harmonic TE incidence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEStaticFlux
open Complex MeasureTheory Metric Set Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology ComplexConjugate

theorem field_mass (R d : ℝ) (hd : 0<d) (S : Source) (hS : Admissible R d S) (i : Fin 3) :
    Integrable (fun q : Plane => NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q) i) ∧
      (∫ q : Plane, ‖NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q) i‖)≤(3/d)*sourceMass S := by
  have hi (j : Fin 3) := StaticPlaneSource.field_integrable d hd (S j) (hS.integrable j)
    (Filter.Eventually.of_forall (hS.gap j)) i j
  have hb (j : Fin 3) := StaticPlaneSource.field_mass d hd (S j) (hS.integrable j)
    (Filter.Eventually.of_forall (hS.gap j)) i j
  simp_rw [NewtonSeparatedResponse.response_plane]
  refine ⟨integrable_finset_sum Finset.univ (fun j _ => hi j),?_⟩
  calc
    _ ≤ ∫ q : Plane, ∑ j : Fin 3, ‖StaticPlaneSource.field (S j) i j q‖ :=
      integral_mono_ae (integrable_finset_sum Finset.univ (fun j _ => hi j)).norm
        (integrable_finset_sum Finset.univ (fun j _ => (hi j).norm))
        (Filter.Eventually.of_forall (fun q => norm_sum_le _ _))
    _ = ∑ j : Fin 3, ∫ q : Plane, ‖StaticPlaneSource.field (S j) i j q‖ :=
      integral_finset_sum _ (fun j _ => (hi j).norm)
    _ ≤ ∑ j : Fin 3, (3/d)*(∫ y, ‖S j y‖) := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem static_mass (A : Index →₀ ℂ) : ∃ B : ℝ, 0≤B ∧ ∀ (R d : ℝ), 0<d →
    ∀ (S : Source), Admissible R d S → Integrable (staticMixed S A) ∧
      (∫ q : Plane, ‖staticMixed S A q‖)≤(6*B/d)*sourceMass S := by
  obtain ⟨B,hB,hH⟩ := RestrictedTEMagnetic.magnetic_bounded A
  refine ⟨B,hB,?_⟩
  intro R d hd S hS
  let F := fun q i => NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q) i
  have hf (i : Fin 3) := field_mass R d hd S hS i
  have hm (i : Fin 3) := (RestrictedTEMagnetic.magnetic_continuous A i).comp MaxwellPlaneTail.planePoint_continuous
  have hc : AEStronglyMeasurable (staticMixed S A) :=
    ((hf 0).1.aestronglyMeasurable.mul (hm 1).star.aestronglyMeasurable).sub
      ((hf 1).1.aestronglyMeasurable.mul (hm 0).star.aestronglyMeasurable)
  have hb (q : Plane) : ‖staticMixed S A q‖≤B*(‖F q 0‖+‖F q 1‖) := by
    change ‖F q 0*star (magnetic A (MaxwellPlaneTail.planePoint q) 1)-
      F q 1*star (magnetic A (MaxwellPlaneTail.planePoint q) 0)‖≤_
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_star]
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (hH _ 1) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hH _ 0) (norm_nonneg _))).trans_eq (by ring)
  have hg := ((hf 0).1.norm.add (hf 1).1.norm).const_mul B
  have hi := hg.mono' hc (Filter.Eventually.of_forall hb)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ q : Plane, B*(‖F q 0‖+‖F q 1‖) := integral_mono_ae hi.norm hg (Filter.Eventually.of_forall hb)
    _ = B*((∫ q : Plane, ‖F q 0‖)+(∫ q : Plane, ‖F q 1‖)) := by
      rw [integral_const_mul,integral_add (hf 0).1.norm (hf 1).1.norm]
    _ ≤ B*((3/d)*sourceMass S+(3/d)*sourceMass S) :=
      mul_le_mul_of_nonneg_left (add_le_add (hf 0).2 (hf 1).2) hB
    _ = _ := by ring

theorem dynamic_integrable (A : Index →₀ ℂ) (R d : ℝ) (hR : 0≤R) (hd : 0<d)
    (S : Source) (hS : Admissible R d S) : Integrable (dynamicMixed S A) := by
  obtain ⟨K,hK,T,hT,hTR,hb⟩ := RestrictedTECoherentTail.error_tail A R hR
  have hc := error_continuous R d hd S hS A
  have hl : IntegrableOn (coherentError S A) (closedBall (0 : Plane) T) :=
    hc.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) T)
  have ht := PlaneInverseCube.tail_integrable T (K*sourceMass S) (by linarith)
    hc.aestronglyMeasurable.restrict (hb d hd S hS)
  have he : {q : Plane | T<‖q‖}=(closedBall (0 : Plane) T)ᶜ := by ext q; simp
  rw [he] at ht
  have herr : Integrable (coherentError S A) := by
    simpa only [union_compl_self,integrableOn_univ] using hl.union ht
  obtain ⟨B,hB,hs⟩ := static_mass A
  apply (herr.add (hs R d hd S hS).1).congr
  filter_upwards with q
  simp [coherentError]

end OQ14.RestrictedTEStaticFlux
#print axioms OQ14.RestrictedTEStaticFlux.field_mass
#print axioms OQ14.RestrictedTEStaticFlux.static_mass
#print axioms OQ14.RestrictedTEStaticFlux.dynamic_integrable
