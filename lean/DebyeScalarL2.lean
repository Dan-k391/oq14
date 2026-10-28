import WeakDebyeScalar
import RegularBallGlobal

/-! Actual bounded radial multiplication and weak Debye scalars in volume L2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.DebyeScalarL2
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.WeakDebyeScalar
  OQ14.ExteriorHelmholtz OQ14.ExteriorGreen OQ14.WeakHelmholtzRegularity
abbrev ScalarL2 := PolarMomentEnergy.ScalarL2

def clipped (R : ℝ) (E : Fin 3 → ScalarL2) (x : Space) : ℂ :=
  (closedBall (0 : Space) R).indicator (radialDot (fun j => E j)) x

theorem clipped_memLp (R : ℝ) (E : Fin 3 → ScalarL2) : MemLp (clipped R E) 2 volume := by
  have hj (j : Fin 3) : MemLp ((closedBall (0 : Space) R).indicator
      (fun x => (x j : ℂ)*E j x)) 2 volume := by
    apply (Lp.memLp (E j)).of_le_mul (c := |R|)
    · exact (((coordinate j).continuous.measurable.aestronglyMeasurable.mul
        (Lp.memLp (E j)).aestronglyMeasurable).indicator measurableSet_closedBall)
    · filter_upwards with x
      by_cases hx : x ∈ closedBall (0 : Space) R
      · rw [indicator_of_mem hx, norm_mul]
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have hn : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
        simpa only [Complex.norm_real] using (PiLp.norm_apply_le x j).trans (hn.trans (le_abs_self R))
      · simp only [indicator_of_not_mem hx, norm_zero]
        positivity
  have h := ((hj 0).add (hj 1)).add (hj 2)
  convert h using 1
  funext x
  by_cases hx : x ∈ closedBall (0 : Space) R <;>
    simp [clipped, radialDot, hx, Fin.sum_univ_three]

def datum (R : ℝ) (E : Fin 3 → ScalarL2) : ScalarL2 :=
  (clipped_memLp R E).toLp (clipped R E)

theorem datum_actual (R : ℝ) (E : Fin 3 → ScalarL2) :
    (datum R E : Space → ℂ) =ᵐ[volume] clipped R E := (clipped_memLp R E).coeFn_toLp

theorem clipped_weak (R : ℝ) (k : ℂ) (E : Fin 3 → ScalarL2)
    (hw : IsWeakHelmholtz k (ball 0 R) (radialDot (fun j => E j))) :
    IsWeakHelmholtz k (ball 0 R) (clipped R E) := by
  intro φ hφ hc hs
  calc
    (∫ x, clipped R E x * (laplacian φ x + k^2*φ x)) =
        ∫ x, radialDot (fun j => E j) x * (laplacian φ x + k^2*φ x) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ closedBall (0 : Space) R
      · simp [clipped, hx]
      · have hn : x ∉ tsupport φ := fun h => hx (ball_subset_closedBall (hs h))
        rw [laplacian_zero_of_not_tsupport hn, image_eq_zero_of_nmem_tsupport hn]
        simp
    _ = 0 := hw φ hφ hc hs

theorem datum_weak (R : ℝ) (k : ℂ) (E : Fin 3 → ScalarL2)
    (hhelm : ∀ j, IsWeakHelmholtz k (ball 0 R) (E j))
    (hdiv : ∀ φ : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 R → (∑ j : Fin 3, ∫ x, E j x * dcoord φ x j) = 0) :
    IsWeakHelmholtz k (ball 0 R) (datum R E) :=
  ComplexKernelRadialBasis.weak_congr_ae k (ball 0 R) _ _ (datum_actual R E)
    (clipped_weak R k E (WeakDebyeScalar.weak_helmholtz _ k (fun j => E j)
      (fun j => (Lp.memLp (E j)).locallyIntegrable (by norm_num)) hhelm hdiv))

theorem regular_moment (R : ℝ) (hR : 0 < R) (k : ℂ) (hk : k ≠ 0)
    (E : Fin 3 → ScalarL2)
    (hhelm : ∀ j, IsWeakHelmholtz k (ball 0 R) (E j))
    (hdiv : ∀ φ : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ ball 0 R → (∑ j : Fin 3, ∫ x, E j x * dcoord φ x j) = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo 0 R),
      (r : ℂ) * RadialMoment.moment (datum R E) (SphericalMomentEquation.angularPolynomial p) r =
        c * RadialOriginSelection.regular l k r :=
  RegularBallGlobal.weak_moment R hR k hk (datum R E) (datum_weak R k E hhelm hdiv) p l hp hh

end OQ14.DebyeScalarL2
#print axioms OQ14.DebyeScalarL2.clipped_memLp
#print axioms OQ14.DebyeScalarL2.datum_actual
#print axioms OQ14.DebyeScalarL2.datum_weak
#print axioms OQ14.DebyeScalarL2.regular_moment
