import DebyeCalculus
import WeakAnnularMoment

/-! The radial Debye scalar of an arbitrary weak divergence-free Helmholtz vector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.WeakDebyeScalar
open MeasureTheory Set OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.ExteriorGreen
  OQ14.WeakHelmholtzRegularity OQ14.WeakAnnularMoment OQ14.DebyeCalculus

def radialDot (E : Fin 3 → Space → ℂ) (x : Space) : ℂ := ∑ j, (x j : ℂ) * E j x

theorem weak_helmholtz (Ω : Set Space) (k : ℂ) (E : Fin 3 → Space → ℂ)
    (hE : ∀ j, LocallyIntegrable (E j))
    (hhelm : ∀ j, IsWeakHelmholtz k Ω (E j))
    (hdiv : ∀ φ : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∑ j : Fin 3, ∫ x, E j x * dcoord φ x j) = 0) :
    IsWeakHelmholtz k Ω (radialDot E) := by
  intro φ hφ hc hs
  let L : Space → ℂ := fun x => laplacian φ x + k^2 * φ x
  have hLc : Continuous L := (laplacian_continuous hφ).add (continuous_const.mul hφ.continuous)
  have hcompact : HasCompactSupport (laplacian φ) := by
    apply hc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (laplacian_zero_of_not_tsupport hn)
  have hLcpt : HasCompactSupport L := hcompact.add hc.mul_left
  have hA (j : Fin 3) : Integrable (fun x => E j x * ((x j : ℂ) * L x)) :=
    integrable_mul_compact _ _ (hE j)
      ((coordinate j).continuous.mul hLc) hLcpt.mul_left
  have hB (j : Fin 3) : Integrable (fun x => E j x * dcoord φ x j) :=
    integrable_mul_compact _ _ (hE j) (partial_continuous (hφ.of_le (by simp)) j)
      (hc.fderiv_apply ℝ (basis j))
  have htest (j : Fin 3) :
      (∫ x, E j x * ((x j : ℂ) * L x)) + 2 * (∫ x, E j x * dcoord φ x j) = 0 := by
    have ht := hhelm j (fun x => (x j : ℂ)*φ x)
      ((coordinate j).contDiff.mul hφ) hc.mul_left
      (tsupport_mul_subset_right.trans hs)
    have he : (fun x => E j x * (laplacian (fun y => (y j : ℂ)*φ y) x + k^2*((x j : ℂ)*φ x))) =
        fun x => E j x * ((x j : ℂ)*L x) + 2*(E j x*dcoord φ x j) := by
      funext x
      rw [show (fun y : Space => (y j : ℂ)*φ y) = (fun y => radialVector φ y j) from rfl,
        radialVector_laplacian φ x hφ.contDiffAt j]
      dsimp [L]
      ring
    rw [he, integral_add (hA j) ((hB j).const_mul 2), integral_const_mul] at ht
    exact ht
  have hsum : (∑ j : Fin 3, ∫ x, E j x * ((x j : ℂ)*L x)) = 0 := by
    have h := congrArg (fun f : Fin 3 → ℂ => ∑ j, f j) (funext htest)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hdiv φ hφ hc hs,
      mul_zero, add_zero, Finset.sum_const_zero] at h
    exact h
  change (∫ x, radialDot E x * L x) = 0
  have he : (fun x => radialDot E x * L x) = fun x => ∑ j, E j x * ((x j : ℂ)*L x) := by
    funext x
    simp only [radialDot, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finset_sum _ (fun j _ => hA j)]
  exact hsum

end OQ14.WeakDebyeScalar
#print axioms OQ14.WeakDebyeScalar.weak_helmholtz
