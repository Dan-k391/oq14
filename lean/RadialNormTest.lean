import ExteriorGreen
import HarmonicPolynomial

/-! # Actual smooth annular tests and their radial harmonic Laplacian -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialNormTest

open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.GreenKernel
  OQ14.ExteriorHelmholtz OQ14.ExteriorGreen OQ14.HelmholtzTestCalculus
open scoped Topology

def radialNorm (η : ℝ → ℂ) (x : Space) : ℂ := η ‖x‖

theorem radialNorm_partial (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    dcoord (radialNorm η) x i = deriv η ‖x‖ * unitCoordinate i x :=
  radial_composition_partial η _ x hx (hη.differentiable (by simp) _).hasDerivAt i

theorem radialNorm_second_partial (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    dcoord (fun y => dcoord (radialNorm η) y i) x i =
      deriv (deriv η) ‖x‖ * (x i : ℂ)^2 / (‖x‖ : ℂ)^2 +
        deriv η ‖x‖ * (1/(‖x‖ : ℂ) - (x i : ℂ)^2/(‖x‖ : ℂ)^3) := by
  have hη' : ContDiff ℝ (⊤ : ℕ∞) (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have hd := (hη'.contDiffAt.comp x (contDiffAt_norm ℝ hx)).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun y : Space => deriv η ‖y‖) x at hd
  have he : (fun y => dcoord (radialNorm η) y i) =ᶠ[𝓝 x]
      (fun y => deriv η ‖y‖ * unitCoordinate i y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact radialNorm_partial η hη y hy i
  have he' := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) he.fderiv_eq
  change dcoord _ x i = dcoord _ x i at he'
  rw [he', partial_mul hd (unitCoordinate_differentiableAt i x hx),
    unitCoordinate_partial i i x hx]
  rw [radial_composition_partial (deriv η) _ x hx
    (hη'.differentiable (by simp) _).hasDerivAt i]
  simp only [ite_true, unitCoordinate]
  push_cast
  ring

theorem radialNorm_laplacian (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (x : Space) (hx : x ≠ 0) :
    laplacian (radialNorm η) x =
      deriv (deriv η) ‖x‖ + 2/(‖x‖ : ℂ)*deriv η ‖x‖ := by
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  simp only [laplacian, radialNorm_second_partial η hη x hx, Fin.sum_univ_three]
  calc
    _ = deriv (deriv η) ‖x‖ *
        ((x 0 : ℂ)^2+(x 1 : ℂ)^2+(x 2 : ℂ)^2)/(‖x‖ : ℂ)^2 +
      deriv η ‖x‖ * (3/(‖x‖ : ℂ) -
        ((x 0 : ℂ)^2+(x 1 : ℂ)^2+(x 2 : ℂ)^2)/(‖x‖ : ℂ)^3) := by ring
    _ = _ := by rw [coordinate_squares]; field_simp [hr]; ring

theorem radialNorm_harmonic_laplacian (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (P : Space → ℂ) (x : Space) (hx : x ≠ 0)
    (hP : ContDiffAt ℝ (⊤ : ℕ∞) P x) (l : ℕ) (hH : laplacian P x = 0)
    (hEuler : (∑ i : Fin 3, (x i : ℂ)*dcoord P x i) = (l : ℂ)*P x) :
    laplacian (fun y => radialNorm η y * P y) x =
      P x * (deriv (deriv η) ‖x‖ + (2*(l : ℂ)+2)/(‖x‖ : ℂ)*deriv η ‖x‖) := by
  have hreg : ContDiffAt ℝ (⊤ : ℕ∞) (radialNorm η) x :=
    hη.contDiffAt.comp x (contDiffAt_norm ℝ hx)
  rw [laplacian_mul _ _ x hreg hP, hH, mul_zero, zero_add,
    radialNorm_laplacian η hη x hx]
  simp only [radialNorm_partial η hη x hx, unitCoordinate, Fin.sum_univ_three] at hEuler ⊢
  push_cast
  linear_combination (2 * deriv η ‖x‖ / (‖x‖ : ℂ)) * hEuler

theorem radialNorm_smooth (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (h0 : 0 ∉ tsupport η) : ContDiff ℝ (⊤ : ℕ∞) (radialNorm η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hzero : η =ᶠ[𝓝 (0 : ℝ)] 0 := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds h0] with y hy
      exact Classical.byContradiction (fun hn => hy (subset_closure hn))
    have he : radialNorm η =ᶠ[𝓝 (0 : Space)] (fun _ => (0 : ℂ)) :=
      hzero.comp_tendsto (by
        simpa using (continuous_norm : Continuous (norm : Space → ℝ)).continuousAt
          (x := (0 : Space)) |>.tendsto)
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact hη.contDiffAt.comp x (contDiffAt_norm ℝ hx)

theorem radialNorm_tsupport (η : ℝ → ℂ) :
    tsupport (radialNorm η) ⊆ (norm : Space → ℝ) ⁻¹' tsupport η := by
  apply closure_minimal _ ((isClosed_tsupport η).preimage continuous_norm)
  intro x hx
  exact subset_closure hx

theorem radialNorm_compact (η : ℝ → ℂ) (hc : HasCompactSupport η) :
    HasCompactSupport (radialNorm η) := by
  obtain ⟨B, hB⟩ := hc.isBounded.subset_closedBall (0 : ℝ)
  apply (isCompact_closedBall (0 : Space) B).of_isClosed_subset (isClosed_tsupport _)
  intro x hx
  have h := hB (radialNorm_tsupport η hx)
  simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_norm] using h

theorem radialNorm_interior (η : ℝ → ℂ) (R : ℝ)
    (hs : tsupport η ⊆ Ioi R) :
    tsupport (radialNorm η) ⊆ {x : Space | R < ‖x‖} :=
  fun _ hx => hs (radialNorm_tsupport η hx)

end OQ14.RadialNormTest

#print axioms OQ14.RadialNormTest.radialNorm_partial
#print axioms OQ14.RadialNormTest.radialNorm_second_partial
#print axioms OQ14.RadialNormTest.radialNorm_laplacian
#print axioms OQ14.RadialNormTest.radialNorm_harmonic_laplacian
#print axioms OQ14.RadialNormTest.radialNorm_smooth
#print axioms OQ14.RadialNormTest.radialNorm_tsupport
#print axioms OQ14.RadialNormTest.radialNorm_compact
#print axioms OQ14.RadialNormTest.radialNorm_interior
