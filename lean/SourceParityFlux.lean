import ParityPlaneColumns
import SourceHerglotzWhole

/-! Actual free-volume and parity-density coherent fluxes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceParityFlux
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation ParityPlaneColumns
open SphereReactionKernel (reaction entryBound entryBound_nonnegative)
open SphereMagneticParity (magneticReaction)
open Maxwell (conjugate)
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space

def electric (h : Bool) (k : ℝ) (ρ σ : Source) (q : Plane) : ℂ :=
  crossProduct (ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q))
    (conjugate (ParityPlaneFields.magnetic h k σ (MaxwellPlaneTail.planePoint q))) 2

def magnetic (e : Bool) (k : ℝ) (ρ σ : Source) (q : Plane) : ℂ :=
  crossProduct (ParityPlaneFields.electric e k ρ (MaxwellPlaneTail.planePoint q))
    (conjugate (MagneticResponse.magnetic k σ (MaxwellPlaneTail.planePoint q))) 2

theorem electric_continuous (h : Bool) (k R d : ℝ) (hd : 0 < d) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) : Continuous (electric h k ρ σ) := by
  have hE (i : Fin 3) := electric_plane_continuous k R d hd ρ hρ i
  have hH (i : Fin 3) := (ParityPlaneFields.magnetic_continuous h k σ hσ.integrable i).comp MaxwellPlaneTail.planePoint_continuous
  exact ((hE 0).mul (hH 1).star).sub ((hE 1).mul (hH 0).star)

theorem magnetic_continuous (e : Bool) (k R d : ℝ) (hd : 0 < d) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) : Continuous (magnetic e k ρ σ) := by
  have hE (i : Fin 3) := (ParityPlaneFields.electric_continuous e k ρ hρ.integrable i).comp MaxwellPlaneTail.planePoint_continuous
  have hH (i : Fin 3) := magnetic_plane_continuous k R d hd σ hσ i
  exact ((hE 0).mul (hH 1).star).sub ((hE 1).mul (hH 0).star)

theorem point_electric_identity (h : Bool) (k : ℝ) (ρ : Source) (q : Plane) (y : Space) (j : Fin 3) :
    crossProduct (ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q))
      (conjugate (fun i => magneticReaction h k (MaxwellPlaneTail.planePoint q) y i j)) 2=
    (if h then -Complex.I else 0)*SourceHerglotzLocal.electricFlux k ρ y j q := by
  change _*star (magneticReaction h k (MaxwellPlaneTail.planePoint q) y 1 j)-
    _*star (magneticReaction h k (MaxwellPlaneTail.planePoint q) y 0 j)=_
  rw [SphereMagneticParity.magnetic_on_plane h k _ y (by rfl) 1 j,
    SphereMagneticParity.magnetic_on_plane h k _ y (by rfl) 0 j]
  cases h <;> norm_num [SphereReactionKernel.sign,Fin.ext_iff,SourceHerglotzLocal.electricFlux,cross_apply,conjugate]
  all_goals simp
  all_goals ring

theorem point_magnetic_identity (e : Bool) (k : ℝ) (σ : Source) (q : Plane) (y : Space) (j : Fin 3) :
    crossProduct (fun i => reaction e k (MaxwellPlaneTail.planePoint q) y i j)
      (conjugate (MagneticResponse.magnetic k σ (MaxwellPlaneTail.planePoint q))) 2=
    (if e then 0 else Complex.I)*SourceHerglotzLocal.magneticFlux k σ y j q := by
  change reaction e k (MaxwellPlaneTail.planePoint q) y 0 j*star _-
    reaction e k (MaxwellPlaneTail.planePoint q) y 1 j*star _=_
  rw [SphereMagneticParity.reaction_on_plane e k _ y (by rfl) 0 j,
    SphereMagneticParity.reaction_on_plane e k _ y (by rfl) 1 j]
  cases e <;> norm_num [SphereReactionKernel.sign,Fin.ext_iff,SourceHerglotzLocal.magneticFlux,cross_apply,conjugate]
  all_goals simp
  all_goals ring

theorem electric_tail (h : Bool) (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (q : Plane) (hq : 2*R < ‖q‖) (hq₂ : 2 ≤ ‖q‖) :
    ‖electric h k ρ σ q‖ ≤ (PointMaxwellTail.tailConstant k k R/‖q‖^3)*sourceMass ρ*sourceMass σ := by
  unfold electric
  rw [magnetic_cross h k σ hσ.integrable]
  apply sum_integral_bound σ hσ.integrable _ (fun j => magnetic_cross_integrable h k σ hσ.integrable _ _ j) _
  intro j
  filter_upwards with y
  by_cases hy : σ j y=0
  · simp [hy]
  · rw [norm_mul,Complex.norm_conj,point_electric_identity,norm_mul]
    have hs : y ∈ closedBall (0 : Space) R := by by_contra hn; exact hy (hσ.support j y hn)
    have ht := SourceHerglotzTail.electric_tail k R d hR hd hk ρ hρ y hs j q hq hq₂
    have hc : ‖(if h then -Complex.I else 0 : ℂ)‖ ≤ 1 := by cases h <;> norm_num
    have hh := (mul_le_mul_of_nonneg_left (mul_le_mul hc ht (norm_nonneg _) (by norm_num)) (norm_nonneg (σ j y)))
    exact hh.trans_eq (by ring)

theorem magnetic_tail (e : Bool) (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (q : Plane) (hq : 2*R < ‖q‖) (hq₂ : 2 ≤ ‖q‖) :
    ‖magnetic e k ρ σ q‖ ≤ (PointMaxwellTail.tailConstant k k R/‖q‖^3)*sourceMass ρ*sourceMass σ := by
  unfold magnetic
  rw [electric_cross e k ρ hρ.integrable]
  apply (sum_integral_bound ρ hρ.integrable _ (fun j => electric_cross_integrable e k ρ hρ.integrable _ _ j)
    ((PointMaxwellTail.tailConstant k k R/‖q‖^3)*sourceMass σ) ?_).trans_eq (by ring)
  intro j
  filter_upwards with y
  by_cases hy : ρ j y=0
  · simp [hy]
  · rw [norm_mul,point_magnetic_identity,norm_mul]
    have hs : y ∈ closedBall (0 : Space) R := by by_contra hn; exact hy (hρ.support j y hn)
    have ht := SourceHerglotzTail.magnetic_tail k R d hR hd hk σ hσ y hs j q hq hq₂
    have hc : ‖(if e then 0 else Complex.I : ℂ)‖ ≤ 1 := by cases e <;> norm_num
    have hh := (mul_le_mul_of_nonneg_left (mul_le_mul hc ht (norm_nonneg _) (by norm_num)) (norm_nonneg (ρ j y)))
    exact hh.trans_eq (by ring)

end OQ14.SourceParityFlux
#print axioms OQ14.SourceParityFlux.electric_continuous
#print axioms OQ14.SourceParityFlux.magnetic_continuous
#print axioms OQ14.SourceParityFlux.point_electric_identity
#print axioms OQ14.SourceParityFlux.point_magnetic_identity
#print axioms OQ14.SourceParityFlux.electric_tail
#print axioms OQ14.SourceParityFlux.magnetic_tail
