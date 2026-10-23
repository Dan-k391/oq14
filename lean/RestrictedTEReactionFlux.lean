import RestrictedTEPointTail
import RestrictedTEScale

/-! Actual parity-electric density versus harmonic TE magnetic whole-plane bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEReactionFlux
open Complex MeasureTheory Metric Set Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal ParityPlaneColumns
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space

def flux (e : Bool) (S : Source) (A : Index →₀ ℂ) (q : Plane) : ℂ :=
  crossProduct (ParityPlaneFields.electric e 1 S (MaxwellPlaneTail.planePoint q))
    (conjugate (magnetic A (MaxwellPlaneTail.planePoint q))) 2

theorem continuous (e : Bool) (S : Source) (hS : ∀ i, Integrable (S i)) (A : Index →₀ ℂ) :
    Continuous (flux e S A) := by
  have he (i : Fin 3) := (ParityPlaneFields.electric_continuous e 1 S hS i).comp MaxwellPlaneTail.planePoint_continuous
  have hh (i : Fin 3) := (RestrictedTEMagnetic.magnetic_continuous A i).comp MaxwellPlaneTail.planePoint_continuous
  exact ((he 0).mul (hh 1).star).sub ((he 1).mul (hh 0).star)

theorem whole_bound (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ (e : Bool) (d : ℝ) (S : Source), Admissible R d S →
      Integrable (flux e S A) ∧ (∫ q : Plane, ‖flux e S A q‖)≤C*sourceMass S := by
  obtain ⟨w,hw,hpos,hb⟩ := RestrictedTEPointTail.global_envelope A R hR
  refine ⟨∫ q, w q,integral_nonneg hpos,?_⟩
  intro e d S hS
  have hbound (q : Plane) : ‖flux e S A q‖≤w q*sourceMass S := by
    unfold flux
    rw [electric_cross e 1 S hS.integrable]
    apply sum_integral_bound S hS.integrable _
      (fun j => electric_cross_integrable e 1 S hS.integrable _ _ j) (w q)
    intro j
    filter_upwards with y
    by_cases hy : S j y=0
    · simp [hy]
    · have hs : y∈closedBall (0 : Space) R := by by_contra hn; exact hy (hS.support j y hn)
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb e y hs j q) (norm_nonneg (S j y))).trans_eq (by ring)
  have hi := (hw.mul_const (sourceMass S)).mono' (continuous e S hS.integrable A).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  refine ⟨hi,?_⟩
  have hm := integral_mono_ae hi.norm (hw.mul_const (sourceMass S)) (Filter.Eventually.of_forall hbound)
  simpa only [integral_mul_const] using hm

theorem smul (e : Bool) (S : Source) (c : ℂ) (A : Index →₀ ℂ) (q : Plane) :
    flux e S (c • A) q=conj c*flux e S A q := by
  simp [flux,RestrictedTEScale.magnetic_smul,cross_apply,conjugate]
  ring

theorem whole_scaled_bound (A : Index →₀ ℂ) (R : ℝ) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ (e : Bool) (d : ℝ) (S : Source), Admissible R d S → ∀ c : ℂ,
      Integrable (flux e S (c • A)) ∧ (∫ q : Plane, ‖flux e S (c • A) q‖)≤C*sourceMass S*‖c‖ := by
  obtain ⟨C,hC,hb⟩ := whole_bound A R hR
  refine ⟨C,hC,?_⟩
  intro e d S hS c
  rw [show flux e S (c • A)=(fun q => conj c*flux e S A q) from funext (smul e S c A)]
  refine ⟨(hb e d S hS).1.const_mul _,?_⟩
  simp only [norm_mul,norm_conj,integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (hb e d S hS).2 (norm_nonneg c)).trans_eq (by ring)

end OQ14.RestrictedTEReactionFlux
#print axioms OQ14.RestrictedTEReactionFlux.continuous
#print axioms OQ14.RestrictedTEReactionFlux.whole_bound
#print axioms OQ14.RestrictedTEReactionFlux.smul
#print axioms OQ14.RestrictedTEReactionFlux.whole_scaled_bound
