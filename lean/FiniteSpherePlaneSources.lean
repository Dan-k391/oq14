import PlaneSourceKernel
import StaticPlaneInclusions

/-! Actual physical and trial finite-ball sources satisfy the plane geometry and L1 error. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSpherePlaneSources
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open scoped Topology
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def trialSource (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) : Source :=
  fun j x => ∑ l : ι, (ball (p l) (r l)).indicator (fun _ => P l j) x

omit [Fintype ι] [DecidableEq ι] in
theorem material_admissible (p : ι → Space) (r : ι → ℝ) (χ R gap : ℝ) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p r χ hχ)) (hdr : d.radius=R)
    (hh : ∀ l, gap+r l ≤ |p l 2|) (u : VectorFourier.VectorL2) :
    Admissible R gap (DynamicVolume.source (FiniteSphereStatic.coefficient p r χ hχ) u) := by
  have hc (x : Space) (hx : x ∉ closedBall 0 R) :
      (FiniteSphereStatic.coefficient p r χ hχ).value (VectorFourier.coordinateMap x)=0 := by
    apply d.ballZero x
    simpa only [hdr] using hx
  exact ⟨fun j => DynamicVolume.source_integrable _ u R hc j,
    fun j x hx => DynamicVolume.source_zero _ u R hc j x hx,
    fun j => StaticPlaneInclusions.material_gap p r χ gap hχ hh u j⟩

theorem trial_admissible (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (R gap : ℝ)
    (hinside : ∀ l, ‖p l‖+r l ≤ R) (hh : ∀ l, gap+r l ≤ |p l 2|) :
    Admissible R gap (trialSource p r P) := by
  have hmem (x : Space) (j : Fin 3) (hx : trialSource p r P j x ≠ 0) : ∃ l, x ∈ ball (p l) (r l) := by
    by_contra hn
    push_neg at hn
    apply hx
    unfold trialSource
    exact Finset.sum_eq_zero (fun l _ => indicator_of_not_mem (hn l) _)
  refine ⟨?_, ?_, ?_⟩
  · intro j
    exact (FiniteSphereReaction.source_integrable p r P j).congr (FiniteSphereStatic.sumSource_ae p r P j)
  · intro j x hx
    by_contra hn
    obtain ⟨l,hl⟩ := hmem x j hn
    have hd : ‖x-p l‖ < r l := by simpa only [mem_ball, dist_eq_norm] using hl
    have ht := norm_add_le (x-p l) (p l)
    rw [sub_add_cancel] at ht
    apply hx
    simp only [mem_closedBall, dist_zero_right]
    linarith [hinside l]
  · intro j x hx
    obtain ⟨l,hl⟩ := hmem x j hx
    exact StaticPlaneInclusions.ball_gap (p l) (r l) gap (hh l) x hl

def errorConstant (χ ρ δ k R b A M : ℝ) : ℝ :=
  3*(Real.sqrt χ*FiniteSphereSmallError.errorConstant (ι := ι) χ ρ δ k R b A M*
    Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ))

omit [DecidableEq ι] in
theorem inverse_source_mass (p : ι → Space) (ρ a χ δ R k b A M : ℝ) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorFourier.VectorL2) (E : ι → Vector)
    (he : FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b A M hχ d f E) :
    sourceMass (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
      (ParityMaterialField.solution d k (b/a) f)-
        trialSource p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l))) ≤
      errorConstant (ι := ι) χ ρ δ k R b A M*a^3 := by
  unfold sourceMass
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => he.2.2 j)
  have hright : (∑ _j : Fin 3, (Real.sqrt χ*FiniteSphereSmallError.errorConstant (ι := ι) χ ρ δ k R b A M*
      Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ))*a^3) = errorConstant (ι := ι) χ ρ δ k R b A M*a^3 := by
    rw [Fin.sum_univ_three]
    unfold errorConstant
    ring
  simpa only [Pi.sub_apply, trialSource] using hh.trans_eq hright

end OQ14.FiniteSpherePlaneSources
#print axioms OQ14.FiniteSpherePlaneSources.material_admissible
#print axioms OQ14.FiniteSpherePlaneSources.trial_admissible
#print axioms OQ14.FiniteSpherePlaneSources.inverse_source_mass
