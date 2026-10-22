import SourceHerglotzTail

/-! Actual whole-plane volume-response/Herglotz coherent bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceHerglotzWhole
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation SourceHerglotzLocal
open SphereReactionKernel (entryBound)
open scoped Topology
abbrev Space := FourierL2.Space

def tailConstant (k R T : ℝ) : ℝ := PointMaxwellTail.tailConstant k k R*PlaneInverseCube.diskConstant/T

def electricConstant (k R T d : ℝ) : ℝ :=
  2*entryBound k*(PlaneMaxwellLocal.electricCoefficient k R T*((Real.pi+PlaneInverseCube.diskConstant)/d))+
    tailConstant k R T

def magneticConstant (k R T d : ℝ) : ℝ :=
  4*entryBound k*|k| * PlaneMaxwellSharp.gradientMass k R T d+tailConstant k R T

private theorem whole_from_parts (f : Plane → ℂ) (T L U M : ℝ)
    (hl : IntegrableOn f (closedBall 0 T) ∧ (∫ q : Plane in closedBall 0 T, ‖f q‖) ≤ L*M)
    (hu : IntegrableOn f {q : Plane | T < ‖q‖} ∧
      (∫ q : Plane in {q : Plane | T < ‖q‖}, ‖f q‖) ≤ U*M) :
    Integrable f ∧ (∫ q : Plane, ‖f q‖) ≤ (L+U)*M := by
  have hs : {q : Plane | T < ‖q‖}=(closedBall (0 : Plane) T)ᶜ := by
    ext q
    simp only [mem_setOf_eq, mem_compl_iff, mem_closedBall, dist_zero_right, not_le]
  rw [hs] at hu
  have hi : Integrable f := by
    have h := hl.1.union hu.1
    simpa only [union_compl_self, integrableOn_univ] using h
  refine ⟨hi, ?_⟩
  rw [← integral_add_compl isClosed_closedBall.measurableSet hi.norm]
  exact (add_le_add hl.2 hu.2).trans_eq (by ring)

theorem electric_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (ρ : Source) (hρ : Admissible R d ρ)
    (z : Space) (hz : z ∈ closedBall 0 R) (m : Fin 3) :
    Integrable (electricFlux k ρ z m) ∧ (∫ q : Plane, ‖electricFlux k ρ z m q‖) ≤
      electricConstant k R T d*sourceMass ρ := by
  have ht := SourceHerglotzTail.electric_tail_mass k R d hR hd hk ρ hρ z hz m T hT hTR
  apply whole_from_parts _ T _ _ _ (electric_local_mass k R T d hd ρ hρ z m)
  exact ⟨ht.1, ht.2.trans_eq (by unfold tailConstant; ring)⟩

theorem magnetic_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hdM : d ≤ T+R) (ρ : Source) (hρ : Admissible R d ρ)
    (z : Space) (hz : z ∈ closedBall 0 R) (j : Fin 3) :
    Integrable (magneticFlux k ρ z j) ∧ (∫ q : Plane, ‖magneticFlux k ρ z j q‖) ≤
      magneticConstant k R T d*sourceMass ρ := by
  have ht := SourceHerglotzTail.magnetic_tail_mass k R d hR hd hk ρ hρ z hz j T hT hTR
  apply whole_from_parts _ T _ _ _ (magnetic_local_mass k R T d hd hdM ρ hρ z j)
  exact ⟨ht.1, ht.2.trans_eq (by unfold tailConstant; ring)⟩

theorem electric_sub_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (z : Space) (hz : z ∈ closedBall 0 R) (m : Fin 3) :
    Integrable (fun q => electricFlux k ρ z m q-electricFlux k σ z m q) ∧
    (∫ q : Plane, ‖electricFlux k ρ z m q-electricFlux k σ z m q‖) ≤
      electricConstant k R T d*sourceMass (ρ-σ) := by
  have he (q : Plane) : electricFlux k (ρ-σ) z m q=electricFlux k ρ z m q-electricFlux k σ z m q := by
    unfold electricFlux
    rw [electric_plane_sub k R d hd ρ σ hρ hσ q]
    simp [cross_apply, Maxwell.conjugate]
  have hefun := funext he
  simpa only [he, hefun] using
    electric_mass k R T d hR hd hk hT hTR (ρ-σ) (admissible_sub R d ρ σ hρ hσ) z hz m

theorem magnetic_sub_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hdM : d ≤ T+R)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (z : Space) (hz : z ∈ closedBall 0 R) (j : Fin 3) :
    Integrable (fun q => magneticFlux k ρ z j q-magneticFlux k σ z j q) ∧
    (∫ q : Plane, ‖magneticFlux k ρ z j q-magneticFlux k σ z j q‖) ≤
      magneticConstant k R T d*sourceMass (ρ-σ) := by
  have he (q : Plane) : magneticFlux k (ρ-σ) z j q=magneticFlux k ρ z j q-magneticFlux k σ z j q := by
    unfold magneticFlux
    rw [magnetic_plane_sub k R d hd ρ σ hρ hσ q]
    simp [cross_apply, Maxwell.conjugate]
    ring
  have hefun := funext he
  simpa only [he, hefun] using
    magnetic_mass k R T d hR hd hk hT hTR hdM (ρ-σ) (admissible_sub R d ρ σ hρ hσ) z hz j

end OQ14.SourceHerglotzWhole
#print axioms OQ14.SourceHerglotzWhole.electric_mass
#print axioms OQ14.SourceHerglotzWhole.magnetic_mass
#print axioms OQ14.SourceHerglotzWhole.electric_sub_mass
#print axioms OQ14.SourceHerglotzWhole.magnetic_sub_mass
