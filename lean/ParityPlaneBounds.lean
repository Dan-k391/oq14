import ParityPlaneColumns

/-! Whole-plane bounds for genuine parity density fluxes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityPlaneBounds
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation ParityPlaneFields ParityPlaneColumns
open SphereReactionKernel (reaction)
open SphereMagneticParity (magneticReaction)
open Maxwell (conjugate)
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space

def flux (e h : Bool) (k : ℝ) (ρ σ : Source) (q : Plane) : ℂ :=
  crossProduct (ParityPlaneFields.electric e k ρ (MaxwellPlaneTail.planePoint q))
    (conjugate (ParityPlaneFields.magnetic h k σ (MaxwellPlaneTail.planePoint q))) 2

theorem point_magnetic_bound (e h : Bool) (k R d : ℝ) (σ : Source) (hσ : Admissible R d σ)
    (x y : Space) (j : Fin 3) (C : ℝ)
    (hb : ∀ z ∈ closedBall (0 : Space) R, ∀ m : Fin 3,
      ‖HerglotzParityPlane.flux e h k x y z j m‖ ≤ C) :
    ‖crossProduct (fun i => reaction e k x y i j)
      (conjugate (ParityPlaneFields.magnetic h k σ x)) 2‖ ≤ C*sourceMass σ := by
  rw [magnetic_cross h k σ hσ.integrable]
  apply sum_integral_bound σ hσ.integrable _ (fun m => magnetic_cross_integrable h k σ hσ.integrable x _ m) C
  intro m
  filter_upwards with z
  by_cases hz : σ m z=0
  · simp [hz]
  · rw [norm_mul,Complex.norm_conj]
    have hs : z ∈ closedBall (0 : Space) R := by by_contra hn; exact hz (hσ.support m z hn)
    exact (mul_le_mul_of_nonneg_left (hb z hs m) (norm_nonneg (σ m z))).trans_eq (by ring)

theorem density_bound (e h : Bool) (k R d : ℝ) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) (q : Plane) (C : ℝ)
    (hb : ∀ y z : Space, y ∈ closedBall 0 R → z ∈ closedBall 0 R → ∀ j m : Fin 3,
      ‖HerglotzParityPlane.flux e h k (MaxwellPlaneTail.planePoint q) y z j m‖ ≤ C) :
    ‖flux e h k ρ σ q‖ ≤ C*sourceMass ρ*sourceMass σ := by
  unfold flux
  rw [electric_cross e k ρ hρ.integrable]
  apply (sum_integral_bound ρ hρ.integrable _
    (fun j => electric_cross_integrable e k ρ hρ.integrable _ _ j) (C*sourceMass σ) ?_).trans_eq (by ring)
  intro j
  filter_upwards with y
  by_cases hy : ρ j y=0
  · simp [hy]
  · rw [norm_mul]
    have hs : y ∈ closedBall (0 : Space) R := by by_contra hn; exact hy (hρ.support j y hn)
    have hh := point_magnetic_bound e h k R d σ hσ (MaxwellPlaneTail.planePoint q) y j C
      (fun z hz m => hb y z hs hz j m)
    exact (mul_le_mul_of_nonneg_left hh (norm_nonneg (ρ j y))).trans_eq (by ring)

theorem flux_continuous (e h : Bool) (k : ℝ) (ρ σ : Source)
    (hρ : ∀ j, Integrable (ρ j)) (hσ : ∀ j, Integrable (σ j)) : Continuous (flux e h k ρ σ) := by
  have hE (i : Fin 3) := (electric_continuous e k ρ hρ i).comp MaxwellPlaneTail.planePoint_continuous
  have hH (i : Fin 3) := (magnetic_continuous h k σ hσ i).comp MaxwellPlaneTail.planePoint_continuous
  exact ((hE 0).mul (hH 1).star).sub ((hE 1).mul (hH 0).star)

theorem whole_bound (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e h : Bool) (d : ℝ) (ρ σ : Source),
      Admissible R d ρ → Admissible R d σ →
      Integrable (flux e h k ρ σ) ∧
        (∫ q : Plane, ‖flux e h k ρ σ q‖) ≤ C*sourceMass ρ*sourceMass σ := by
  obtain ⟨w,hw,hpos,hb⟩ := HerglotzPointTail.global_envelope k R hR hk
  refine ⟨∫ q, w q,integral_nonneg hpos,?_⟩
  intro e h d ρ σ hρ hσ
  have hb' (q : Plane) : ‖flux e h k ρ σ q‖ ≤ w q*sourceMass ρ*sourceMass σ :=
    density_bound e h k R d ρ σ hρ hσ q (w q) (fun y z hy hz j m =>
      (HerglotzParityPlane.flux_norm_le e h k (MaxwellPlaneTail.planePoint q) y z (by rfl) j m).trans
        (hb y z hy hz j m q))
  have hi := ((hw.mul_const (sourceMass ρ)).mul_const (sourceMass σ)).mono'
    (flux_continuous e h k ρ σ hρ.integrable hσ.integrable).aestronglyMeasurable (Filter.Eventually.of_forall hb')
  refine ⟨hi,?_⟩
  have hm := integral_mono_ae hi.norm ((hw.mul_const (sourceMass ρ)).mul_const (sourceMass σ))
    (Filter.Eventually.of_forall hb')
  simpa only [integral_mul_const] using hm

end OQ14.ParityPlaneBounds
#print axioms OQ14.ParityPlaneBounds.point_magnetic_bound
#print axioms OQ14.ParityPlaneBounds.density_bound
#print axioms OQ14.ParityPlaneBounds.flux_continuous
#print axioms OQ14.ParityPlaneBounds.whole_bound
