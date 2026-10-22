import SourceHerglotzLocal
import PointSourceColumns
import MixedPointTail

/-! Genuine density-integrated source/Herglotz normal-flux tails. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceHerglotzTail
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation SourceHerglotzLocal
open SphereReactionKernel (J)
open SphereMagneticKernel (K)
open Maxwell (conjugate)
open scoped ComplexConjugate Topology

private theorem sum_integral_bound (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (f : Fin 3 → Maxwell.Space → ℂ) (hi : ∀ j, Integrable (f j)) (C : ℝ)
    (hb : ∀ j, ∀ᵐ y, ‖f j y‖ ≤ C*‖ρ j y‖) :
    ‖∑ j : Fin 3, ∫ y, f j y‖ ≤ C*sourceMass ρ := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 3, ∫ y, ‖f j y‖ := Finset.sum_le_sum (fun j _ => norm_integral_le_integral_norm _)
    _ ≤ ∑ j : Fin 3, C*(∫ y, ‖ρ j y‖) := Finset.sum_le_sum (fun j _ =>
      (integral_mono_ae (hi j).norm ((hρ j).norm.const_mul C) (hb j)).trans_eq (integral_const_mul _ _))
    _ = _ := by unfold sourceMass; rw [Finset.mul_sum]

private theorem source_in_ball (R d : ℝ) (ρ : Source) (hρ : Admissible R d ρ)
    (j : Fin 3) (y : Maxwell.Space) (hy : ρ j y ≠ 0) : y ∈ closedBall 0 R := by
  by_contra hn
  exact hy (hρ.support j y hn)

theorem electric_tail (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (ρ : Source) (hρ : Admissible R d ρ) (z : Maxwell.Space) (hz : z ∈ closedBall 0 R)
    (m : Fin 3) (q : Plane) (hq : 2*R < ‖q‖) (hq₂ : 2 ≤ ‖q‖) :
    ‖electricFlux k ρ z m q‖ ≤ (PointMaxwellTail.tailConstant k k R/‖q‖^3)*sourceMass ρ := by
  let x := MaxwellPlaneTail.planePoint q
  let v := fun i => K k (x-z) i m
  change ‖crossProduct (ExteriorContinuity.electric k ρ x) (conjugate v) 2‖ ≤ _
  rw [PointSourceColumns.electric_cross_columns k R d hd ρ hρ q v]
  apply sum_integral_bound ρ hρ.integrable _
    (fun j => PointSourceColumns.electric_cross_integrable k R d hd ρ hρ q v j)
  intro j
  filter_upwards with y
  by_cases hy : ρ j y=0
  · simp [hy]
  · rw [norm_mul]
    have hb := MixedPointTail.electric_tail k R hR hk x y z
      (by simpa only [x, MaxwellPlaneTail.planePoint_norm] using hq)
      (by simpa only [x, MaxwellPlaneTail.planePoint_norm] using hq₂) (by rfl)
      (source_in_ball R d ρ hρ j y hy) hz j m
    have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (ρ j y))
    simpa only [MixedPointTail.electricRegular, x, v, MaxwellPlaneTail.planePoint_norm, mul_comm] using hh

theorem magnetic_tail (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (ρ : Source) (hρ : Admissible R d ρ) (z : Maxwell.Space) (hz : z ∈ closedBall 0 R)
    (j : Fin 3) (q : Plane) (hq : 2*R < ‖q‖) (hq₂ : 2 ≤ ‖q‖) :
    ‖magneticFlux k ρ z j q‖ ≤ (PointMaxwellTail.tailConstant k k R/‖q‖^3)*sourceMass ρ := by
  let x := MaxwellPlaneTail.planePoint q
  let v := fun i => J k (x-z) i j
  change ‖crossProduct v (conjugate (MagneticResponse.magnetic k ρ x)) 2‖ ≤ _
  rw [PointSourceColumns.magnetic_cross_columns k R d hd ρ hρ q v]
  apply sum_integral_bound ρ hρ.integrable _
    (fun m => PointSourceColumns.magnetic_cross_integrable k R d hd ρ hρ q v m)
  intro m
  filter_upwards with y
  by_cases hy : ρ m y=0
  · simp [hy]
  · rw [norm_mul, Complex.norm_conj]
    have hb := MixedPointTail.magnetic_tail k R hR hk x z y
      (by simpa only [x, MaxwellPlaneTail.planePoint_norm] using hq)
      (by simpa only [x, MaxwellPlaneTail.planePoint_norm] using hq₂) (by rfl)
      hz (source_in_ball R d ρ hρ m y hy) j m
    have hh := mul_le_mul_of_nonneg_left hb (norm_nonneg (ρ m y))
    simpa only [MixedPointTail.regularMagnetic, x, v, MaxwellPlaneTail.planePoint_norm, mul_comm] using hh

theorem electric_tail_mass (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (ρ : Source) (hρ : Admissible R d ρ) (z : Maxwell.Space) (hz : z ∈ closedBall 0 R)
    (m : Fin 3) (T : ℝ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) :
    IntegrableOn (electricFlux k ρ z m) {q : Plane | T < ‖q‖} ∧
    (∫ q : Plane in {q : Plane | T < ‖q‖}, ‖electricFlux k ρ z m q‖) ≤
      (PointMaxwellTail.tailConstant k k R*sourceMass ρ)*PlaneInverseCube.diskConstant/T := by
  have hm : AEStronglyMeasurable (electricFlux k ρ z m) (volume.restrict {q : Plane | T < ‖q‖}) :=
    (electric_continuous k R d hd ρ hρ z m).aestronglyMeasurable.restrict
  have hb (q : Plane) (hq : T < ‖q‖) : ‖electricFlux k ρ z m q‖ ≤
      (PointMaxwellTail.tailConstant k k R*sourceMass ρ)/‖q‖^3 :=
    (electric_tail k R d hR hd hk ρ hρ z hz m q (by linarith) (by linarith)).trans_eq (by ring)
  exact ⟨PlaneInverseCube.tail_integrable T _ (by linarith) hm hb,
    PlaneInverseCube.tail_integral_bound T _ (by linarith) hm hb⟩

theorem magnetic_tail_mass (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hk : k ≠ 0)
    (ρ : Source) (hρ : Admissible R d ρ) (z : Maxwell.Space) (hz : z ∈ closedBall 0 R)
    (j : Fin 3) (T : ℝ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) :
    IntegrableOn (magneticFlux k ρ z j) {q : Plane | T < ‖q‖} ∧
    (∫ q : Plane in {q : Plane | T < ‖q‖}, ‖magneticFlux k ρ z j q‖) ≤
      (PointMaxwellTail.tailConstant k k R*sourceMass ρ)*PlaneInverseCube.diskConstant/T := by
  have hm : AEStronglyMeasurable (magneticFlux k ρ z j) (volume.restrict {q : Plane | T < ‖q‖}) :=
    (magnetic_continuous k R d hd ρ hρ z j).aestronglyMeasurable.restrict
  have hb (q : Plane) (hq : T < ‖q‖) : ‖magneticFlux k ρ z j q‖ ≤
      (PointMaxwellTail.tailConstant k k R*sourceMass ρ)/‖q‖^3 :=
    (magnetic_tail k R d hR hd hk ρ hρ z hz j q (by linarith) (by linarith)).trans_eq (by ring)
  exact ⟨PlaneInverseCube.tail_integrable T _ (by linarith) hm hb,
    PlaneInverseCube.tail_integral_bound T _ (by linarith) hm hb⟩

end OQ14.SourceHerglotzTail
#print axioms OQ14.SourceHerglotzTail.electric_tail
#print axioms OQ14.SourceHerglotzTail.magnetic_tail
#print axioms OQ14.SourceHerglotzTail.electric_tail_mass
#print axioms OQ14.SourceHerglotzTail.magnetic_tail_mass
