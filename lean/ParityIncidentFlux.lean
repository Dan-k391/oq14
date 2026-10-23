import ParityPlaneBounds
import FiniteSphereMaxwell

/-! Genuine whole-plane parity density versus finite-incident flux bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityIncidentFlux
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation ParityPlaneColumns
open SphereReactionKernel (reaction)
open SphereMagneticParity (magneticReaction)
open Maxwell (conjugate)
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
variable {ι : Type*} [Fintype ι]

def flux (e : Bool) (k : ℝ) (ρ : Source) (h : ι → Bool) (p : ι → Space)
    (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) : ℂ :=
  crossProduct (ParityPlaneFields.electric e k ρ (MaxwellPlaneTail.planePoint q))
    (conjugate (FiniteHerglotzFlux.magnetic k h p j A (MaxwellPlaneTail.planePoint q))) 2

theorem finite_magnetic_cross (k : ℝ) (h : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (x : Space) (v : Vector) :
    crossProduct v (conjugate (FiniteHerglotzFlux.magnetic k h p j A x)) 2=
      ∑ s, conj (A s)*crossProduct v (conjugate (fun i => magneticReaction (h s) k x (p s) i (j s))) 2 := by
  classical
  change v 0*star (∑ s, A s*magneticReaction (h s) k x (p s) 1 (j s))-
    v 1*star (∑ s, A s*magneticReaction (h s) k x (p s) 0 (j s))=_
  simp only [star_sum,star_mul]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simp [cross_apply,conjugate]
  ring

theorem whole_bound (k R : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (e : Bool) (d : ℝ) (ρ : Source), Admissible R d ρ →
      ∀ (h : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ),
      (∀ s, p s ∈ closedBall 0 R) → Integrable (flux e k ρ h p j A) ∧
        (∫ q : Plane, ‖flux e k ρ h p j A q‖) ≤ C*sourceMass ρ*(∑ s, ‖A s‖) := by
  classical
  obtain ⟨w,hw,hpos,hb⟩ := HerglotzPointTail.global_envelope k R hR hk
  refine ⟨∫ q, w q,integral_nonneg hpos,?_⟩
  intro e d ρ hρ h p j A hp
  have hbound (q : Plane) : ‖flux e k ρ h p j A q‖ ≤ w q*sourceMass ρ*(∑ s, ‖A s‖) := by
    unfold flux
    rw [electric_cross e k ρ hρ.integrable]
    apply (sum_integral_bound ρ hρ.integrable _
      (fun m => electric_cross_integrable e k ρ hρ.integrable _ _ m) (w q*(∑ s, ‖A s‖)) ?_).trans_eq (by ring)
    intro m
    filter_upwards with y
    by_cases hy : ρ m y=0
    · simp [hy]
    · rw [norm_mul,finite_magnetic_cross]
      have hs : y ∈ closedBall (0 : Space) R := by by_contra hn; exact hy (hρ.support m y hn)
      have hh : ‖∑ s, conj (A s)*crossProduct (fun i => reaction e k (MaxwellPlaneTail.planePoint q) y i m)
          (conjugate (fun i => magneticReaction (h s) k (MaxwellPlaneTail.planePoint q) (p s) i (j s))) 2‖ ≤
          w q*(∑ s, ‖A s‖) := by
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ s, ‖A s‖*w q := Finset.sum_le_sum (fun s _ => by
            rw [norm_mul,Complex.norm_conj]
            exact mul_le_mul_of_nonneg_left
              ((HerglotzParityPlane.flux_norm_le e (h s) k (MaxwellPlaneTail.planePoint q) y (p s) (by rfl) m (j s)).trans
                (hb y (p s) hs (hp s) m (j s) q)) (norm_nonneg _))
          _ = _ := by rw [← Finset.sum_mul]; ring
      exact (mul_le_mul_of_nonneg_left hh (norm_nonneg (ρ m y))).trans_eq (by ring)
  have hE (i : Fin 3) := (ParityPlaneFields.electric_continuous e k ρ hρ.integrable i).comp MaxwellPlaneTail.planePoint_continuous
  have hH (i : Fin 3) : Continuous (fun q : Plane => FiniteHerglotzFlux.magnetic k h p j A (MaxwellPlaneTail.planePoint q) i) :=
    (continuous_iff_continuousAt.mpr (fun x => (FiniteSphereMaxwell.magnetic_differentiable k h p j A x i).continuousAt)).comp
      MaxwellPlaneTail.planePoint_continuous
  have hc : Continuous (flux e k ρ h p j A) := ((hE 0).mul (hH 1).star).sub ((hE 1).mul (hH 0).star)
  have hi := ((hw.mul_const (sourceMass ρ)).mul_const (∑ s, ‖A s‖)).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  refine ⟨hi,?_⟩
  have hm := integral_mono_ae hi.norm ((hw.mul_const (sourceMass ρ)).mul_const (∑ s, ‖A s‖))
    (Filter.Eventually.of_forall hbound)
  simpa only [integral_mul_const] using hm

theorem incident_electric_zero (k : ℝ) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ)
    (x : Space) (hx : x 2=0) (i : Fin 3) (hi : i ≠ 2) :
    FiniteHerglotzFlux.electric k (fun _ => true) p j A x i=0 := by
  unfold FiniteHerglotzFlux.electric
  apply Finset.sum_eq_zero
  intro s _
  rw [SphereMagneticParity.reaction_on_plane true k x (p s) hx i (j s)]
  simp [SphereReactionKernel.sign,hi]

theorem incident_cross_zero (k : ℝ) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ)
    (x : Space) (hx : x 2=0) (v : Vector) :
    crossProduct (FiniteHerglotzFlux.electric k (fun _ => true) p j A x) (conjugate v) 2=0 := by
  change _*star (v 1)-_*star (v 0)=0
  rw [incident_electric_zero k p j A x hx 0 (by decide),incident_electric_zero k p j A x hx 1 (by decide)]
  ring

end OQ14.ParityIncidentFlux
#print axioms OQ14.ParityIncidentFlux.finite_magnetic_cross
#print axioms OQ14.ParityIncidentFlux.whole_bound
#print axioms OQ14.ParityIncidentFlux.incident_electric_zero
#print axioms OQ14.ParityIncidentFlux.incident_cross_zero
