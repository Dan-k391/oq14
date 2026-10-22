import FiniteHerglotzFlux
import SourceHerglotzWhole

/-! Actual finite point-parity incident fields paired with a genuine volume response. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceHerglotzFinite
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation SourceHerglotzLocal
open SphereReactionKernel (J reaction sign)
open SphereMagneticKernel (K)
open SphereMagneticParity (magneticReaction magnetic_on_plane reaction_on_plane)
open Maxwell (Vector conjugate)
open scoped ComplexConjugate Topology
variable {ι : Type*} [Fintype ι]
abbrev Space := FourierL2.Space

def electricMixed (k : ℝ) (ρ : Source) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (q : Plane) : ℂ :=
  crossProduct (ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q))
    (conjugate (FiniteHerglotzFlux.magnetic k e p j A (MaxwellPlaneTail.planePoint q))) 2

def magneticMixed (k : ℝ) (ρ : Source) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (q : Plane) : ℂ :=
  crossProduct (FiniteHerglotzFlux.electric k e p j A (MaxwellPlaneTail.planePoint q))
    (conjugate (MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q))) 2

private theorem magnetic_selector (e : Bool) (k : ℝ) (q : Plane) (z : Space) (m : Fin 3) (v : Vector) :
    crossProduct v (conjugate (fun i => magneticReaction e k (MaxwellPlaneTail.planePoint q) z i m)) 2 =
      (if e then -Complex.I else 0)*crossProduct v
        (conjugate (fun i => K k (MaxwellPlaneTail.planePoint q-z) i m)) 2 := by
  change v 0*star (magneticReaction e k (MaxwellPlaneTail.planePoint q) z 1 m)-
    v 1*star (magneticReaction e k (MaxwellPlaneTail.planePoint q) z 0 m)=_
  rw [magnetic_on_plane e k _ z (by rfl) 1 m, magnetic_on_plane e k _ z (by rfl) 0 m]
  cases e <;> norm_num [sign, Fin.ext_iff, cross_apply, conjugate, Complex.star_def, Complex.conj_I]
  all_goals simp
  all_goals ring

private theorem electric_selector (e : Bool) (k : ℝ) (q : Plane) (z : Space) (j : Fin 3) (v : Vector) :
    crossProduct (fun i => reaction e k (MaxwellPlaneTail.planePoint q) z i j) (conjugate v) 2 =
      (if e then 0 else Complex.I)*crossProduct (fun i => J k (MaxwellPlaneTail.planePoint q-z) i j)
        (conjugate v) 2 := by
  change reaction e k (MaxwellPlaneTail.planePoint q) z 0 j*star (v 1)-
    reaction e k (MaxwellPlaneTail.planePoint q) z 1 j*star (v 0)=_
  rw [reaction_on_plane e k _ z (by rfl) 0 j, reaction_on_plane e k _ z (by rfl) 1 j]
  cases e <;> norm_num [sign, Fin.ext_iff, cross_apply, conjugate]
  all_goals simp
  all_goals ring

theorem electric_expansion (k : ℝ) (ρ : Source) (e : ι → Bool) (p : ι → Space)
    (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) :
    electricMixed k ρ e p j A q=∑ s, (conj (A s)*(if e s then -Complex.I else 0))*electricFlux k ρ (p s) (j s) q := by
  classical
  unfold electricMixed FiniteHerglotzFlux.magnetic
  let E := ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q)
  change E 0*star (∑ s, A s*magneticReaction (e s) k (MaxwellPlaneTail.planePoint q) (p s) 1 (j s))-
    E 1*star (∑ s, A s*magneticReaction (e s) k (MaxwellPlaneTail.planePoint q) (p s) 0 (j s))=_
  simp only [star_sum, star_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = conj (A s)*crossProduct E (conjugate (fun i =>
      magneticReaction (e s) k (MaxwellPlaneTail.planePoint q) (p s) i (j s))) 2 := by
      simp [cross_apply, conjugate, Complex.star_def]
      ring
    _ = _ := by rw [magnetic_selector]; unfold electricFlux; dsimp only [E]; ring

theorem magnetic_expansion (k : ℝ) (ρ : Source) (e : ι → Bool) (p : ι → Space)
    (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) :
    magneticMixed k ρ e p j A q=∑ s, (A s*(if e s then 0 else Complex.I))*magneticFlux k ρ (p s) (j s) q := by
  classical
  unfold magneticMixed FiniteHerglotzFlux.electric
  let H := MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q)
  change (∑ s, A s*reaction (e s) k (MaxwellPlaneTail.planePoint q) (p s) 0 (j s))*star (H 1)-
    (∑ s, A s*reaction (e s) k (MaxwellPlaneTail.planePoint q) (p s) 1 (j s))*star (H 0)=_
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = A s*crossProduct (fun i => reaction (e s) k (MaxwellPlaneTail.planePoint q) (p s) i (j s)) (conjugate H) 2 := by
      simp [cross_apply, conjugate]
      ring
    _ = _ := by rw [electric_selector]; unfold magneticFlux; dsimp only [H]; ring

private theorem finite_mass (f : ι → Plane → ℂ) (A : ι → ℂ) (C : ℝ)
    (hi : ∀ s, Integrable (f s)) (hb : ∀ s, (∫ q : Plane, ‖f s q‖) ≤ C*‖A s‖) :
    Integrable (fun q => ∑ s, f s q) ∧ (∫ q : Plane, ‖∑ s, f s q‖) ≤ C*(∑ s, ‖A s‖) := by
  have hs := integrable_finset_sum Finset.univ (fun s _ => hi s)
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∫ q : Plane, ∑ s, ‖f s q‖ := integral_mono_ae hs.norm
      (integrable_finset_sum Finset.univ (fun s _ => (hi s).norm))
      (Filter.Eventually.of_forall (fun q => norm_sum_le _ _))
    _ = ∑ s, ∫ q : Plane, ‖f s q‖ := integral_finset_sum _ (fun s _ => (hi s).norm)
    _ ≤ ∑ s, C*‖A s‖ := Finset.sum_le_sum (fun s _ => hb s)
    _ = _ := (Finset.mul_sum _ _ _).symm

private theorem magnetic_weight_bound (e : Bool) (a : ℂ) : ‖conj a*(if e then -Complex.I else 0)‖ ≤ ‖a‖ := by
  cases e <;> simp [norm_mul]

private theorem electric_weight_bound (e : Bool) (a : ℂ) : ‖a*(if e then 0 else Complex.I)‖ ≤ ‖a‖ := by
  cases e <;> simp [norm_mul]

theorem electric_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (ρ : Source) (hρ : Admissible R d ρ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (hp : ∀ s, p s ∈ closedBall 0 R) :
    Integrable (electricMixed k ρ e p j A) ∧ (∫ q : Plane, ‖electricMixed k ρ e p j A q‖) ≤
      SourceHerglotzWhole.electricConstant k R T d*sourceMass ρ*(∑ s, ‖A s‖) := by
  have ht (s : ι) := SourceHerglotzWhole.electric_mass k R T d hR hd hk hT hTR ρ hρ (p s) (hp s) (j s)
  have he : electricMixed k ρ e p j A=(fun q => ∑ s,
    (conj (A s)*(if e s then -Complex.I else 0))*electricFlux k ρ (p s) (j s) q) := funext (electric_expansion k ρ e p j A)
  rw [he]
  apply finite_mass _ A (SourceHerglotzWhole.electricConstant k R T d*sourceMass ρ) (fun s => (ht s).1.const_mul _)
  intro s
  simp only [norm_mul, integral_const_mul]
  rw [← norm_mul]
  change ‖conj (A s)*(if e s then -Complex.I else 0)‖*
    (∫ q : Plane, ‖electricFlux k ρ (p s) (j s) q‖) ≤
      (SourceHerglotzWhole.electricConstant k R T d*sourceMass ρ)*‖A s‖
  calc
    _ ≤ ‖A s‖*(SourceHerglotzWhole.electricConstant k R T d*sourceMass ρ) :=
      mul_le_mul (magnetic_weight_bound (e s) (A s)) (ht s).2
        (integral_nonneg (fun q => norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem magnetic_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hdM : d ≤ T+R) (ρ : Source) (hρ : Admissible R d ρ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (hp : ∀ s, p s ∈ closedBall 0 R) :
    Integrable (magneticMixed k ρ e p j A) ∧ (∫ q : Plane, ‖magneticMixed k ρ e p j A q‖) ≤
      SourceHerglotzWhole.magneticConstant k R T d*sourceMass ρ*(∑ s, ‖A s‖) := by
  have ht (s : ι) := SourceHerglotzWhole.magnetic_mass k R T d hR hd hk hT hTR hdM ρ hρ (p s) (hp s) (j s)
  have he : magneticMixed k ρ e p j A=(fun q => ∑ s,
    (A s*(if e s then 0 else Complex.I))*magneticFlux k ρ (p s) (j s) q) := funext (magnetic_expansion k ρ e p j A)
  rw [he]
  apply finite_mass _ A (SourceHerglotzWhole.magneticConstant k R T d*sourceMass ρ) (fun s => (ht s).1.const_mul _)
  intro s
  simp only [norm_mul, integral_const_mul]
  rw [← norm_mul]
  change ‖A s*(if e s then 0 else Complex.I)‖*
    (∫ q : Plane, ‖magneticFlux k ρ (p s) (j s) q‖) ≤
      (SourceHerglotzWhole.magneticConstant k R T d*sourceMass ρ)*‖A s‖
  calc
    _ ≤ ‖A s‖*(SourceHerglotzWhole.magneticConstant k R T d*sourceMass ρ) :=
      mul_le_mul (electric_weight_bound (e s) (A s)) (ht s).2
        (integral_nonneg (fun q => norm_nonneg _)) (norm_nonneg _)
    _ = _ := by ring

theorem electric_sub_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (hp : ∀ s, p s ∈ closedBall 0 R) :
    Integrable (fun q => electricMixed k ρ e p j A q-electricMixed k σ e p j A q) ∧
    (∫ q : Plane, ‖electricMixed k ρ e p j A q-electricMixed k σ e p j A q‖) ≤
      SourceHerglotzWhole.electricConstant k R T d*sourceMass (ρ-σ)*(∑ s, ‖A s‖) := by
  have he (q : Plane) : electricMixed k (ρ-σ) e p j A q=electricMixed k ρ e p j A q-electricMixed k σ e p j A q := by
    unfold electricMixed
    rw [electric_plane_sub k R d hd ρ σ hρ hσ q]
    simp [cross_apply, conjugate]
  have hefun := funext he
  simpa only [he, hefun] using electric_mass k R T d hR hd hk hT hTR (ρ-σ)
    (admissible_sub R d ρ σ hρ hσ) e p j A hp

theorem magnetic_sub_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hdM : d ≤ T+R)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (hp : ∀ s, p s ∈ closedBall 0 R) :
    Integrable (fun q => magneticMixed k ρ e p j A q-magneticMixed k σ e p j A q) ∧
    (∫ q : Plane, ‖magneticMixed k ρ e p j A q-magneticMixed k σ e p j A q‖) ≤
      SourceHerglotzWhole.magneticConstant k R T d*sourceMass (ρ-σ)*(∑ s, ‖A s‖) := by
  have he (q : Plane) : magneticMixed k (ρ-σ) e p j A q=magneticMixed k ρ e p j A q-magneticMixed k σ e p j A q := by
    unfold magneticMixed
    rw [magnetic_plane_sub k R d hd ρ σ hρ hσ q]
    simp [cross_apply, conjugate]
    ring
  have hefun := funext he
  simpa only [he, hefun] using magnetic_mass k R T d hR hd hk hT hTR hdM (ρ-σ)
    (admissible_sub R d ρ σ hρ hσ) e p j A hp
end OQ14.SourceHerglotzFinite
#print axioms OQ14.SourceHerglotzFinite.electric_expansion
#print axioms OQ14.SourceHerglotzFinite.magnetic_expansion
#print axioms OQ14.SourceHerglotzFinite.electric_mass
#print axioms OQ14.SourceHerglotzFinite.magnetic_mass

#print axioms OQ14.SourceHerglotzFinite.electric_sub_mass
#print axioms OQ14.SourceHerglotzFinite.magnetic_sub_mass
