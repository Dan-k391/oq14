import DebyeScalarL2
import ComplexMagneticDivergence
import ComplexMagneticResponse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexMagneticDebye
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.WeakDebyeScalar OQ14.ExteriorHelmholtz OQ14.ExteriorGreen
  OQ14.WeakHelmholtzRegularity OQ14.RegionalMaxwellHelmholtz
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

def coordinates (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (i : Fin 3) : DebyeScalarL2.ScalarL2 :=
  ComplexMagneticResponse.response (ModalWeightedMode.coefficient n hn) z 1 1 u i

theorem coordinates_ae (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) (i : Fin 3) :
    (coordinates n hn z u i : Space → ℂ) =ᵐ[volume.restrict (ball 0 1)]
      fun x => ComplexSphereMaxwell.magnetic n hn z u x i :=
  ae_restrict_of_ae_restrict_of_subset ball_subset_closedBall
    (ComplexMagneticResponse.response_actual (ModalWeightedMode.coefficient n hn) z 1 1 u
      (ModalWeightedMode.coefficient_support n hn) i)

theorem coordinate_helmholtz (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) : IsWeakHelmholtz (z*n) (ball 0 1) (coordinates n hn z u i) := by
  intro φ hφ hc hs
  have he := (ae_restrict_iff' measurableSet_ball).mp (coordinates_ae n hn z u i)
  calc
    (∫ x, coordinates n hn z u i x * (laplacian φ x + (z*n)^2*φ x)) =
        ∫ x, ComplexSphereMaxwell.magnetic n hn z u x i * (laplacian φ x + (z*n)^2*φ x) := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      by_cases hxb : x ∈ ball (0 : Space) 1
      · rw [hx hxb]
      · have ht : x ∉ tsupport φ := fun h => hxb (hs h)
        rw [laplacian_zero_of_not_tsupport ht, image_eq_zero_of_nmem_tsupport ht]
        simp
    _ = 0 := ComplexMagneticHelmholtz.interior n hn z hz 1 (le_refl 1) u hker i φ hφ hc hs

theorem divergence (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ ball 0 1) :
    (∑ j : Fin 3, ∫ x, coordinates n hn z u j x * dcoord φ x j) = 0 := by
  let f : Test (ball 0 1) := ⟨φ,hφ,hc,hs⟩
  have h := ComplexMagneticDivergence.interior n hn z hz 1 (le_refl 1) u hker f
  change (∑ j : Fin 3, ∫ x, ComplexSphereMaxwell.magnetic n hn z u x j * dcoord φ x j) = 0 at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_ball).mp (coordinates_ae n hn z u j)] with x hx
  by_cases hxb : x ∈ ball (0 : Space) 1
  · rw [hx hxb]
  · have ht : x ∉ tsupport φ := fun h => hxb (hs h)
    simp [dcoord, fderiv_of_not_mem_tsupport ℝ ht]

theorem scalar_weak (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0) :
    IsWeakHelmholtz (z*n) (ball 0 1) (DebyeScalarL2.datum 1 (coordinates n hn z u)) :=
  DebyeScalarL2.datum_weak 1 (z*n) _ (coordinate_helmholtz n hn z hz u hker)
    (divergence n hn z hz u hker)

theorem scalar_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2) :
    (DebyeScalarL2.datum 1 (coordinates n hn z u) : Space → ℂ) =ᵐ[volume.restrict (ball 0 1)]
      radialDot (fun j x => ComplexSphereMaxwell.magnetic n hn z u x j) := by
  have hall := ae_all_iff.mpr (fun j => coordinates_ae n hn z u j)
  filter_upwards [ae_restrict_of_ae (DebyeScalarL2.datum_actual 1 (coordinates n hn z u)), hall,
    ae_restrict_mem measurableSet_ball] with x hx he hball
  rw [hx]
  unfold DebyeScalarL2.clipped
  rw [indicator_of_mem (ball_subset_closedBall hball)]
  unfold radialDot
  apply Finset.sum_congr rfl
  intro j _
  change (x j : ℂ) * coordinates n hn z u j x = _
  rw [he j]

def radialCoefficient (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (p : HarmonicPolynomial.Poly) (r : ℝ) : ℂ :=
  ∫ ω : Sphere, (∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) *
    ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) j) *
      SphericalMomentEquation.angularPolynomial p ω ∂angularMeasure

theorem moment_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (p : HarmonicPolynomial.Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo 0 1),
      RadialMoment.moment (DebyeScalarL2.datum 1 (coordinates n hn z u))
        (SphericalMomentEquation.angularPolynomial p) r = (r : ℂ) * radialCoefficient n hn z u p r := by
  have hp := PolarMomentAE.polar_ae ((ae_restrict_iff' measurableSet_ball).mp (scalar_actual n hn z u))
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun r hr => hr.1
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hp, ae_restrict_mem measurableSet_Ioo] with r hr hri
  rw [radialCoefficient, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hr] with ω hω
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hri.1]
  have hball : r • (ω : Space) ∈ ball (0 : Space) 1 := by
    simpa only [mem_ball, dist_zero_right, hnorm] using hri.2
  rw [hω hball]
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

#print axioms OQ14.ComplexMagneticDebye.coordinate_helmholtz
#print axioms OQ14.ComplexMagneticDebye.divergence
#print axioms OQ14.ComplexMagneticDebye.scalar_weak
#print axioms OQ14.ComplexMagneticDebye.regular_radial_coefficient
#print axioms OQ14.ComplexMagneticDebye.coordinates_ae
#print axioms OQ14.ComplexMagneticDebye.scalar_actual
#print axioms OQ14.ComplexMagneticDebye.moment_actual
end OQ14.ComplexMagneticDebye
