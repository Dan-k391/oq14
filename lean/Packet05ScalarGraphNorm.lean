import Packet05GreenRepresentativeBounds
import Packet06MaxwellScalarEquation
import Packet05ChartH2Uniform
import Packet05GraphH2Norm

/-! Fixed-bump scalar graph norms from physical local L² representatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarGraphNorm
open MeasureTheory Set Metric OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.ConicalGradientGraph OQ14.Packet05GreenRepresentativeBounds OQ14.Packet05GraphH2Norm

private theorem bump_bound (χ : ContDiffBump (0 : Maxwell.Space)) (x : Maxwell.Space) : ‖bump χ x‖ ≤ 1 := by
  change ‖(χ x : ℂ)‖ ≤ 1
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg χ.nonneg] using χ.le_one

theorem derivative_bound (χ : ContDiffBump (0 : Maxwell.Space)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i x, ‖dcoord (bump χ) x i‖ ≤ K := by
  have hr : ContDiff ℝ (⊤ : ℕ∞) (bump χ) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hreg : ContDiff ℝ 1 (bump χ) := hr.of_le (by simp)
  have hcomp : HasCompactSupport (bump χ) := χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hb (i : Fin 3) : ∃ K : ℝ, ∀ x, ‖dcoord (bump χ) x i‖ ≤ K :=
    (hcomp.fderiv_apply ℝ (basis i)).exists_bound_of_continuous (partial_continuous hreg i)
  choose K hK using hb
  refine ⟨∑ i : Fin 3, max (K i) 0,Finset.sum_nonneg (fun _ _ => le_max_right _ _),?_⟩
  intro i x
  exact (hK i x).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)))

theorem localized_scalar_norms (χ : ContDiffBump (0 : Maxwell.Space)) (U : PotentialData)
    (P : L2Scalar) (D : Fin 3 → L2Scalar)
    (hP : ∀ᵐ x ∂volume, x ∈ closedBall (0 : Maxwell.Space) χ.rOut → P x = U.potential x)
    (hD : ∀ i, ∀ᵐ x ∂volume, x ∈ closedBall (0 : Maxwell.Space) χ.rOut → D i x = U.derivative i x) :
    ∃ K : ℝ, 0 ≤ K ∧ ‖value χ U‖ ≤ ‖P‖ ∧
      ∀ i, ‖gradient χ U i‖ ≤ ‖D i‖ + K*‖P‖ := by
  obtain ⟨K,hK,hKbound⟩ := derivative_bound χ
  have hp : ‖restrictedL2 χ.rOut U.potential (U.potential_memLp χ.rOut)‖ ≤ ‖P‖ := by
    exact ball_norm_le χ.rOut U.potential (U.potential_memLp χ.rOut) P hP
  have hd (i : Fin 3) : ‖restrictedL2 χ.rOut (fun x => U.derivative i x) (U.derivative_memLp χ.rOut i)‖ ≤ ‖D i‖ := by
    exact ball_norm_le χ.rOut _ (U.derivative_memLp χ.rOut i) (D i) (hD i)
  have hreg : ContDiff ℝ (⊤ : ℕ∞) (bump χ) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hcomp : HasCompactSupport (bump χ) := χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hv := OQ14.InteriorTestDensity.scaleL2_norm_le (bump χ) hreg.continuous hcomp
    (restrictedL2 χ.rOut U.potential (U.potential_memLp χ.rOut)) (bump_bound χ)
  refine ⟨K,hK,?_,?_⟩
  · exact hv.trans (by linarith)
  · intro i
    have h1 := OQ14.InteriorTestDensity.scaleL2_norm_le (bump χ) hreg.continuous hcomp
      (restrictedL2 χ.rOut (fun x => U.derivative i x) (U.derivative_memLp χ.rOut i)) (bump_bound χ)
    have h2 := OQ14.InteriorTestDensity.scaleL2_norm_le (fun x => dcoord (bump χ) x i)
      (partial_continuous (hreg.of_le (by simp)) i) (hcomp.fderiv_apply ℝ (basis i))
      (restrictedL2 χ.rOut U.potential (U.potential_memLp χ.rOut)) (hKbound i)
    have hp' := mul_le_mul_of_nonneg_left hp hK
    change ‖_ + _‖ ≤ _
    exact (norm_add_le _ _).trans (by linarith [hd i])


theorem localized_scalar_norms_with_bound (χ : ContDiffBump (0 : Maxwell.Space)) (U : PotentialData)
    (P : L2Scalar) (D : Fin 3 → L2Scalar)
    (hP : ∀ᵐ x ∂volume, x ∈ closedBall (0 : Maxwell.Space) χ.rOut → P x = U.potential x)
    (hD : ∀ i, ∀ᵐ x ∂volume, x ∈ closedBall (0 : Maxwell.Space) χ.rOut → D i x = U.derivative i x)
    (K : ℝ) (hK : 0 ≤ K) (hKbound : ∀ i x, ‖dcoord (bump χ) x i‖ ≤ K) :
    ‖value χ U‖ ≤ ‖P‖ ∧ ∀ i, ‖gradient χ U i‖ ≤ ‖D i‖ + K*‖P‖ := by
  have hp : ‖restrictedL2 χ.rOut U.potential (U.potential_memLp χ.rOut)‖ ≤ ‖P‖ := by
    exact ball_norm_le χ.rOut U.potential (U.potential_memLp χ.rOut) P hP
  have hd (i : Fin 3) : ‖restrictedL2 χ.rOut (fun x => U.derivative i x) (U.derivative_memLp χ.rOut i)‖ ≤ ‖D i‖ := by
    exact ball_norm_le χ.rOut _ (U.derivative_memLp χ.rOut i) (D i) (hD i)
  have hreg : ContDiff ℝ (⊤ : ℕ∞) (bump χ) := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hcomp : HasCompactSupport (bump χ) := χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
  have hv := OQ14.InteriorTestDensity.scaleL2_norm_le (bump χ) hreg.continuous hcomp
    (restrictedL2 χ.rOut U.potential (U.potential_memLp χ.rOut)) (bump_bound χ)
  refine ⟨?_,?_⟩
  · exact hv.trans (by linarith)
  · intro i
    have h1 := OQ14.InteriorTestDensity.scaleL2_norm_le (bump χ) hreg.continuous hcomp
      (restrictedL2 χ.rOut (fun x => U.derivative i x) (U.derivative_memLp χ.rOut i)) (bump_bound χ)
    have h2 := OQ14.InteriorTestDensity.scaleL2_norm_le (fun x => dcoord (bump χ) x i)
      (partial_continuous (hreg.of_le (by simp)) i) (hcomp.fderiv_apply ℝ (basis i))
      (restrictedL2 χ.rOut U.potential (U.potential_memLp χ.rOut)) (hKbound i)
    have hp' := mul_le_mul_of_nonneg_left hp hK
    change ‖_ + _‖ ≤ _
    exact (norm_add_le _ _).trans (by linarith [hd i])

end OQ14.Packet05ScalarGraphNorm
#print axioms OQ14.Packet05ScalarGraphNorm.derivative_bound
#print axioms OQ14.Packet05ScalarGraphNorm.localized_scalar_norms

#print axioms OQ14.Packet05ScalarGraphNorm.localized_scalar_norms_with_bound
