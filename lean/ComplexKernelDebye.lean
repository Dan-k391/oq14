import DebyeScalarL2
import ComplexSphereDivergence

/-! Genuine radial electric coefficients of arbitrary complex sphere-kernel vectors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexKernelDebye
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.WeakDebyeScalar OQ14.ExteriorHelmholtz OQ14.ComplexKernelResponse
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

def coordinates (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (i : Fin 3) :
    DebyeScalarL2.ScalarL2 := NewtonL2.physicalCoordinate (response (ModalWeightedMode.coefficient n hn) z 1 u) i

theorem divergence (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ball 0 1) :
    (∑ j : Fin 3, ∫ x, coordinates n hn z u j x * dcoord φ x j) = 0 := by
  rw [← ComplexSphereDivergence.actual_divergence n hn z hz u hker φ hφ hc hs]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [NewtonL2.physicalCoordinate_ae (response (ModalWeightedMode.coefficient n hn) z 1 u) j]
    with x hx
  change NewtonL2.physicalCoordinate _ j x * _ = _
  rw [hx]

theorem scalar_weak (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0) :
    WeakHelmholtzRegularity.IsWeakHelmholtz (z*n) (ball 0 1)
      (DebyeScalarL2.datum 1 (coordinates n hn z u)) :=
  DebyeScalarL2.datum_weak 1 (z*n) _
    (ComplexKernelRegularOrigin.interior_ball n hn z hz u hker)
    (divergence n hn z hz u hker)

theorem scalar_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) :
    (DebyeScalarL2.datum 1 (coordinates n hn z u) : Space → ℂ) =ᵐ[volume]
      (closedBall (0 : Space) 1).indicator
        (radialDot (fun j x => response (ModalWeightedMode.coefficient n hn) z 1 u (VectorFourier.coordinateMap x) j)) := by
  have hall := ae_all_iff.mpr (fun j => NewtonL2.physicalCoordinate_ae
    (response (ModalWeightedMode.coefficient n hn) z 1 u) j)
  filter_upwards [DebyeScalarL2.datum_actual 1 (coordinates n hn z u),hall] with x hx he
  rw [hx]
  unfold DebyeScalarL2.clipped
  by_cases hball : x ∈ closedBall (0 : Space) 1
  · rw [indicator_of_mem hball, indicator_of_mem hball]
    unfold radialDot
    apply Finset.sum_congr rfl
    intro j _
    change (x j : ℂ)*NewtonL2.physicalCoordinate _ j x = _
    rw [he j]
  · simp only [indicator_of_not_mem hball]

def radialCoefficient (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (p : HarmonicPolynomial.Poly) (r : ℝ) : ℂ :=
  ∫ ω : Sphere, (∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) *
    response (ModalWeightedMode.coefficient n hn) z 1 u (VectorFourier.coordinateMap (r • (ω : Space))) j) *
      SphericalMomentEquation.angularPolynomial p ω ∂angularMeasure

theorem moment_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (p : HarmonicPolynomial.Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo 0 1),
      RadialMoment.moment (DebyeScalarL2.datum 1 (coordinates n hn z u))
        (SphericalMomentEquation.angularPolynomial p) r = (r : ℂ) * radialCoefficient n hn z u p r := by
  have hp := PolarMomentAE.polar_ae (scalar_actual n hn z u)
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun r hr => hr.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hp, ae_restrict_mem measurableSet_Ioo] with r hr hri
  rw [radialCoefficient, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hr] with ω hω
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hri.1]
  have hball : r • (ω : Space) ∈ closedBall (0 : Space) 1 := by
    simpa only [mem_closedBall, dist_zero_right, hnorm] using hri.2.le
  rw [hω, indicator_of_mem hball]
  simp only [radialDot, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Fin.sum_univ_three]
  ring

theorem regular_radial_coefficient (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo 0 1),
      (r : ℂ)^2 * radialCoefficient n hn z u p r = c * RadialOriginSelection.regular l (z*n) r := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  obtain ⟨c,hc⟩ := RegularBallGlobal.weak_moment 1 (by norm_num) (z*n) (mul_ne_zero hz hn0)
    (DebyeScalarL2.datum 1 (coordinates n hn z u)) (scalar_weak n hn z hz u hker) p l hp hh
  refine ⟨c,?_⟩
  filter_upwards [hc,moment_actual n hn z u p] with r hr hm
  rw [hm] at hr
  simpa only [pow_two, mul_assoc] using hr

end OQ14.ComplexKernelDebye
#print axioms OQ14.ComplexKernelDebye.divergence
#print axioms OQ14.ComplexKernelDebye.scalar_weak
#print axioms OQ14.ComplexKernelDebye.scalar_actual
#print axioms OQ14.ComplexKernelDebye.moment_actual
#print axioms OQ14.ComplexKernelDebye.regular_radial_coefficient
