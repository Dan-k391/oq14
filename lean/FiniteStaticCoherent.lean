import StaticCoherentRemainder
import ParityTotalFlux

/-! Whole-plane dynamic-to-static coherent comparison for actual finite point illuminations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteStaticCoherent
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open StaticCoherentRemainder (staticFlux flux wholeCoefficient)
open Maxwell (conjugate)
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

def staticMixed (k : ℝ) (S : Source) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) : ℂ :=
  crossProduct (NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q))
    (conjugate (ParityTotalFlux.incidentMagnetic k p j A (MaxwellPlaneTail.planePoint q))) 2

theorem static_expansion (k : ℝ) (S : Source) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) :
    staticMixed k S p j A q=∑ s, (conj (A s)*(-Complex.I))*staticFlux k S (p s) (j s) q := by
  classical
  unfold staticMixed ParityTotalFlux.incidentMagnetic FiniteHerglotzFlux.magnetic
  let E := NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q)
  change E 0*star (∑ s, A s*SphereMagneticParity.magneticReaction true k (MaxwellPlaneTail.planePoint q) (p s) 1 (j s))-
    E 1*star (∑ s, A s*SphereMagneticParity.magneticReaction true k (MaxwellPlaneTail.planePoint q) (p s) 0 (j s))=_
  simp only [star_sum,star_mul]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [SphereMagneticParity.magnetic_on_plane true k _ (p s) (by rfl) 1 (j s),
    SphereMagneticParity.magnetic_on_plane true k _ (p s) (by rfl) 0 (j s)]
  norm_num [SphereReactionKernel.sign,Fin.ext_iff,staticFlux,cross_apply,conjugate,Complex.star_def,Complex.conj_I,E]
  simp
  ring

theorem difference_expansion (k : ℝ) (S : Source) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) :
    SourceHerglotzFinite.electricMixed k S (fun _ => true) p j A q-staticMixed k S p j A q=
      ∑ s, (conj (A s)*(-Complex.I))*flux k S (p s) (j s) q := by
  rw [SourceHerglotzFinite.electric_expansion,static_expansion,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp only [ite_true,flux,mul_sub]

theorem whole_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hdM : d ≤ T+R) (S : Source) (hS : Admissible R d S)
    (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (hp : ∀ s, p s ∈ closedBall 0 R) :
    Integrable (fun q => SourceHerglotzFinite.electricMixed k S (fun _ => true) p j A q-staticMixed k S p j A q) ∧
    (∫ q : Plane, ‖SourceHerglotzFinite.electricMixed k S (fun _ => true) p j A q-staticMixed k S p j A q‖) ≤
      wholeCoefficient k R T*sourceMass S*(∑ s, ‖A s‖) := by
  have ht (s : ι) := StaticCoherentRemainder.whole_mass k R T d hR hd hk hT hTR hdM S hS (p s) (hp s) (j s)
  have hi (s : ι) : Integrable (fun q => (conj (A s)*(-Complex.I))*flux k S (p s) (j s) q) := (ht s).1.const_mul _
  have hall := integrable_finset_sum Finset.univ (fun s _ => hi s)
  simp_rw [difference_expansion]
  refine ⟨hall,?_⟩
  calc
    _ ≤ ∫ q : Plane, ∑ s, ‖(conj (A s)*(-Complex.I))*flux k S (p s) (j s) q‖ :=
      integral_mono_ae hall.norm (integrable_finset_sum Finset.univ (fun s _ => (hi s).norm))
        (Filter.Eventually.of_forall (fun q => norm_sum_le _ _))
    _ = ∑ s, ‖A s‖*(∫ q : Plane, ‖flux k S (p s) (j s) q‖) := by
      rw [integral_finset_sum _ (fun s _ => (hi s).norm)]
      simp only [norm_mul,norm_neg,Complex.norm_I,Complex.norm_conj,mul_one,integral_const_mul]
    _ ≤ ∑ s, ‖A s‖*(wholeCoefficient k R T*sourceMass S) :=
      Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (ht s).2 (norm_nonneg _))
    _ = _ := by simp only [← Finset.sum_mul]; ring

end OQ14.FiniteStaticCoherent
#print axioms OQ14.FiniteStaticCoherent.static_expansion
#print axioms OQ14.FiniteStaticCoherent.difference_expansion
#print axioms OQ14.FiniteStaticCoherent.whole_mass
