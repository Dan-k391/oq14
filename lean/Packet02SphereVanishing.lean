import Packet02SurfaceL2
import Packet02DebyeVanishing
import Packet02Surface

/-! Sphere-level consequences once absolute convergence has been established
for the actual products on a fixed sphere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02SphereVanishing
open MeasureTheory Metric OQ14.Maxwell OQ14.ModalWeightedMode OQ14.AngularPower
open OQ14.ModalMeridionalReflection OQ14.WeakDebyeScalar

theorem sphere_radial_zero_of_good_ae (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector) (r : ℝ) (hr : r ≠ 0)
    (hg : ∀ᵐ ω : Sphere ∂angularMeasure, Packet02GoodSet.good n hn u (r • (ω : Space))) :
    ∀ᵐ ω : Sphere ∂angularMeasure, ∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) *
      ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) j = 0 := by
  filter_upwards [hg] with ω hω
  have hz := Packet02MagneticVanishing.radial_zero_good n hn u hu z (r • (ω : Space)) hω
  have he : (r : ℂ) * (∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) *
      ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) j) = 0 := by
    convert hz using 1
    simp only [radialDot, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Fin.sum_univ_three]
    ring
  exact (mul_eq_zero.mp he).resolve_left (Complex.ofReal_ne_zero.mpr hr)
theorem radialCoefficient_zero_of_good_ae (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector) (p : HarmonicPolynomial.Poly)
    (r : ℝ) (hr : r ≠ 0)
    (hg : ∀ᵐ ω : Sphere ∂angularMeasure, Packet02GoodSet.good n hn u (r • (ω : Space))) :
    ComplexMagneticDebye.radialCoefficient n hn z u p r = 0 := by
  unfold ComplexMagneticDebye.radialCoefficient
  apply integral_eq_zero_of_ae
  filter_upwards [hg] with ω hω
  have hz := Packet02MagneticVanishing.radial_zero_good n hn u hu z (r • (ω : Space)) hω
  have he : (r : ℂ) * (∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) *
      ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) j) = 0 := by
    convert hz using 1
    simp only [radialDot, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Fin.sum_univ_three]
    ring
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  simp [(mul_eq_zero.mp he).resolve_left hr']

theorem good_ae_of_joint (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) (r : ℝ)
    (h : ∀ l : Fin 3, Integrable (fun p : Sphere × Space =>
      DynamicVolume.source (coefficient n hn) u l p.2 * Packet02GoodSet.inverseSquare
        (r • (p.1 : Space) - p.2)) (angularMeasure.prod volume)) :
    ∀ᵐ ω : Sphere ∂angularMeasure, Packet02GoodSet.good n hn u (r • (ω : Space)) := by
  exact ae_all_iff.mpr (fun l => (h l).prod_right_ae)

theorem magnetic_integrable_of_joint (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (r : ℝ) (i : Fin 3)
    (h : ∀ j l, Integrable (Packet02Surface.entry z (DynamicVolume.source (coefficient n hn) u) r j l)
      (angularMeasure.prod volume)) :
    Integrable (fun ω : Sphere => ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) i)
      angularMeasure :=
  Packet02Surface.magnetic_integrable_of_joint z (DynamicVolume.source (coefficient n hn) u) r h i

theorem gradient_joint_of_inverseSquare (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (r : ℝ) (j l : Fin 3)
    (h : Integrable (fun p : Sphere × Space => DynamicVolume.source (coefficient n hn) u l p.2 *
      Packet02GoodSet.inverseSquare (r • (p.1 : Space) - p.2)) (angularMeasure.prod volume)) :
    Integrable (Packet02Surface.entry z (DynamicVolume.source (coefficient n hn) u) r j l)
      (angularMeasure.prod volume) := by
  let C := (4 * Real.pi)⁻¹ * Real.exp (‖z‖*(|r|+1)) * (‖z‖*(|r|+1)+1)
  have hs := DynamicVolume.source_integrable (coefficient n hn) u 1 (coefficient_support n hn) l
  have hgrad : Measurable (fun p : Sphere × Space =>
      ComplexGreenKernel.phiGradient z (r • (p.1 : Space) - p.2) j) := by
    apply (ComplexMagneticLocal.gradient_measurable z j).comp
    fun_prop
  have hm : AEStronglyMeasurable (Packet02Surface.entry z (DynamicVolume.source (coefficient n hn) u) r j l)
      (angularMeasure.prod volume) := by
    apply (hs.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul
    exact hgrad.aestronglyMeasurable
  apply ((h.norm).const_mul C).mono' hm
  filter_upwards with p
  by_cases hy : p.2 ∈ closedBall (0 : Space) 1
  · have hy' : ‖p.2‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
    have hxy : ‖r • (p.1 : Space) - p.2‖ ≤ |r|+1 := by
      have h1 := norm_sub_le (r • (p.1 : Space)) p.2
      simp only [norm_smul, Real.norm_eq_abs, sphere_norm, mul_one] at h1
      linarith
    have hb := Packet02GoodSet.gradient_bound_inverseSquare z (|r|+1)
      (r • (p.1 : Space)-p.2) hxy j
    have hi : ‖Packet02GoodSet.inverseSquare (r • (p.1 : Space)-p.2)‖ =
        (‖r • (p.1 : Space)-p.2‖⁻¹)^2 := by simp [Packet02GoodSet.inverseSquare]
    simp only [Packet02Surface.entry, norm_mul, hi]
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg (DynamicVolume.source (coefficient n hn) u l p.2))]
  · simp [Packet02Surface.entry, DynamicVolume.source_zero (coefficient n hn) u 1
      (coefficient_support n hn) l p.2 hy]

theorem good_sphere_ae (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω : Sphere ∂angularMeasure, Packet02GoodSet.good n hn u (r • (ω : Space)) :=
  good_ae_of_joint n hn u r (fun l => Packet02SurfaceL2.inverseSquare_joint n hn u r hr l)

theorem sphere_radial_zero (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector) (r : ℝ) (hr : 0 < r) :
    ∀ᵐ ω : Sphere ∂angularMeasure, ∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) *
      ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) j = 0 :=
  sphere_radial_zero_of_good_ae n hn z u hu r (ne_of_gt hr) (good_sphere_ae n hn u r hr)

theorem radialCoefficient_zero (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector) (p : HarmonicPolynomial.Poly)
    (r : ℝ) (hr : 0 < r) :
    ComplexMagneticDebye.radialCoefficient n hn z u p r = 0 :=
  radialCoefficient_zero_of_good_ae n hn z u hu p r (ne_of_gt hr) (good_sphere_ae n hn u r hr)

theorem magnetic_integrable (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (r : ℝ) (hr : 0 < r) (i : Fin 3) :
    Integrable (fun ω : Sphere => ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) i)
      angularMeasure :=
  magnetic_integrable_of_joint n hn z u r i (fun j l =>
    gradient_joint_of_inverseSquare n hn z u r j l (Packet02SurfaceL2.inverseSquare_joint n hn u r hr l))

#print axioms OQ14.Packet02SphereVanishing.good_sphere_ae
#print axioms OQ14.Packet02SphereVanishing.sphere_radial_zero
#print axioms OQ14.Packet02SphereVanishing.radialCoefficient_zero
#print axioms OQ14.Packet02SphereVanishing.magnetic_integrable
#print axioms OQ14.Packet02SphereVanishing.gradient_joint_of_inverseSquare
#print axioms OQ14.Packet02SphereVanishing.sphere_radial_zero_of_good_ae
#print axioms OQ14.Packet02SphereVanishing.radialCoefficient_zero_of_good_ae
#print axioms OQ14.Packet02SphereVanishing.good_ae_of_joint
#print axioms OQ14.Packet02SphereVanishing.magnetic_integrable_of_joint
end OQ14.Packet02SphereVanishing
