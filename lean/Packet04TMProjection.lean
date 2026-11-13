import Packet04RadialCurl
import Packet04VectorTests

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet04TMProjection
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.HarmonicPolynomial OQ14.SphericalMomentEquation
  OQ14.Packet04WeakSphereMaxwell OQ14.RegionalMaxwellHelmholtz
  OQ14.ComplexSphereMaxwell OQ14.DebyeCalculus
open scoped Topology

/-- Compact radial-vector test on a ball, with a radial test supported away
from the origin. It may cross the material interface. -/
def radialVectorTest (T : ℝ) (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) (i : Fin 3) : Test (ball (0 : Space) T) := by
  have h0 : 0 ∉ tsupport η := fun h => (hs h).1.false
  have ht := test_regular η hη h0 p
  have htc := test_compact η hc p
  refine ⟨fun x => (x i : ℂ) * test η p x,
    (coordinate i).contDiff.mul ht, htc.mul_left, ?_⟩
  intro x hx
  have hh := RadialNormTest.radialNorm_tsupport η
    (tsupport_mul_subset_left (tsupport_mul_subset_right hx))
  simpa [Metric.mem_ball, dist_zero_right] using (hs hh).2

/-- Actual electric Maxwell equation tested by the finite radial harmonic
vector, including tests that cross r=1. -/
theorem actual_radial_test (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) :
    (∫ x, ∑ i : Fin 3, electric n hn z T u x i *
      curl (radialVector (test η p)) x i) =
      I*z * ∫ x, ∑ i : Fin 3, magnetic n hn z u x i *
        radialVector (test η p) x i := by
  apply Packet04VectorTests.weak_vector_curl (ball (0 : Space) T)
    (electric n hn z T u) (magnetic n hn z u) (I*z)
    (electric_local n hn z T u) (ComplexMagneticHelmholtz.magnetic_local n hn z u)
    (fun i f => (actual_maxwell n hn z T hT u hker i f).1)
    (radialVectorTest T η hη hc hs p)

/-- Curl of the radial vector test, again a compact vector test even at the
material interface. -/
def toroidalVectorTest (T : ℝ) (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) (i : Fin 3) : Test (ball (0 : Space) T) := by
  let F := radialVectorTest T η hη hc hs p
  let f := testPartial (WeakCurl.next i) (F (WeakCurl.previous i))
  let g := testPartial (WeakCurl.previous i) (F (WeakCurl.next i))
  refine ⟨fun x => f.val x - g.val x, f.property.1.sub g.property.1,
    by simpa only [sub_eq_add_neg] using f.property.2.1.add (HasCompactSupport.neg' g.property.2.1), ?_⟩
  have ht : tsupport (fun x => f.val x + (-g.val) x) ⊆
      tsupport f.val ∪ tsupport (-g.val) := tsupport_add
  have hg : tsupport (-g.val) = tsupport g.val := by
    unfold tsupport
    ext x
    simp [Function.support]
  rw [hg] at ht
  simpa only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply] using
    ht.trans (union_subset f.property.2.2 g.property.2.2)

/-- Actual Maxwell curl equation with the toroidal vector test. -/
theorem actual_toroidal_test (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) :
    (∫ x, ∑ i : Fin 3, electric n hn z T u x i *
      curl (curl (radialVector (test η p))) x i) =
      I*z * ∫ x, ∑ i : Fin 3, magnetic n hn z u x i *
        curl (radialVector (test η p)) x i := by
  have ht : (fun y j => (toroidalVectorTest T η hη hc hs p j).val y) =
      curl (radialVector (test η p)) := by
    funext y j
    change _ - _ = _
    exact (Packet04VectorTests.curl_component (radialVector (test η p)) y j).symm
  rw [← ht]
  exact Packet04VectorTests.weak_vector_curl (ball (0 : Space) T)
    (electric n hn z T u) (magnetic n hn z u) (I*z)
    (electric_local n hn z T u) (ComplexMagneticHelmholtz.magnetic_local n hn z u)
    (fun i f => (actual_maxwell n hn z T hT u hker i f).1)
    (toroidalVectorTest T η hη hc hs p)

/-- The actual displacement is locally integrable, by kernel source recovery. -/
theorem displacement_local (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0) (i : Fin 3) :
    LocallyIntegrable (fun x => permittivity n hn x * electric n hn z T u x i) := by
  have he := electric_local n hn z T u i
  have hs := (DynamicVolume.source_integrable _ u 1
    (ModalWeightedMode.coefficient_support n hn) i).locallyIntegrable
  have hh := he.add hs
  apply locallyIntegrable_iff.mpr
  intro K hK
  apply (hh.integrableOn_isCompact hK).congr
  filter_upwards [ae_restrict_of_ae (ComplexSphereInterface.source_actual n hn z T hT u hker i)] with x hx
  change electric n hn z T u x i + DynamicVolume.source
    (ModalWeightedMode.coefficient n hn) u i x = _
  rw [hx]
  dsimp [permittivity, electric]
  ring

/-- Actual second Maxwell equation tested by the radial vector harmonic. -/
theorem actual_magnetic_radial_test (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) :
    (∫ x, ∑ i : Fin 3, magnetic n hn z u x i *
      curl (radialVector (test η p)) x i) =
      -(I*z) * ∫ x, ∑ i : Fin 3, (permittivity n hn x * electric n hn z T u x i) *
        radialVector (test η p) x i := by
  apply Packet04VectorTests.weak_vector_curl (ball (0 : Space) T)
    (magnetic n hn z u) (fun x i => permittivity n hn x * electric n hn z T u x i) (-(I*z))
    (ComplexMagneticHelmholtz.magnetic_local n hn z u)
    (displacement_local n hn z T hT u hker)
    (fun i f => (actual_maxwell n hn z T hT u hker i f).2)
    (radialVectorTest T η hη hc hs p)

/-- Polar form of the actual magnetic equation with a radial harmonic test;
this integral identity crosses r=1 and retains the actual dielectric. -/
theorem actual_magnetic_radial_polar (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : AngularPower.Sphere,
      ∑ i : Fin 3, magnetic n hn z u (r • (ω : Space)) i *
        (η r * (r : ℂ)^l * DebyeRadialTrace.angularToroidal p (ω : Space) i)
        ∂AngularPower.angularMeasure) =
      -(I*z) * ∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : AngularPower.Sphere,
      ∑ i : Fin 3, (permittivity n hn (r • (ω : Space)) *
        electric n hn z T u (r • (ω : Space)) i) *
        ((r : ℂ) * ((ω : Space) i : ℂ) * (η r * (r : ℂ)^l *
          complexEvaluate p (ω : Space))) ∂AngularPower.angularMeasure := by
  have h1 := Packet04VectorTests.vector_integrable (ball (0 : Space) T)
    (magnetic n hn z u) (ComplexMagneticHelmholtz.magnetic_local n hn z u)
    (radialVectorTest T η hη hc hs p)
  change Integrable (fun x => ∑ i : Fin 3, magnetic n hn z u x i *
    curl (radialVector (test η p)) x i) at h1
  have h2 : Integrable (fun x => ∑ i : Fin 3,
      (permittivity n hn x * electric n hn z T u x i) * radialVector (test η p) x i) := by
    apply integrable_finset_sum
    intro i _
    exact WeakAnnularMoment.integrable_mul_compact _ _ (displacement_local n hn z T hT u hker i)
      (radialVectorTest T η hη hc hs p i).property.1.continuous
      (radialVectorTest T η hη hc hs p i).property.2.1
  have hh := actual_magnetic_radial_test n hn z T hT u hker η hη hc hs p
  rw [ComplexPolarIntegration.integral_polar_complex _ h1,
    ComplexPolarIntegration.integral_polar_complex _ h2] at hh
  convert hh using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    congr 1
    funext i
    rw [Packet04RadialCurl.radial_test_curl_on_ray η hη p l hp r hr ω i]
  · congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change 0 < r at hr
    dsimp only
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    congr 1
    funext i
    have hnorm : ‖r • (ω : Space)‖ = r := by
      simp [norm_smul, AngularPower.sphere_norm, abs_of_pos hr]
    simp only [radialVector, test, RadialNormTest.radialNorm, hnorm,
      FischerDecomposition.complexEvaluate_smul p l hp, PiLp.smul_apply, smul_eq_mul,
      Complex.ofReal_mul]
    ring

/-- Polar form of the electric Maxwell equation with the toroidal test. -/
theorem actual_toroidal_polar (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1))
    (hharm : formalLaplacian p = 0) :
    (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : AngularPower.Sphere,
      ∑ i : Fin 3, electric n hn z T u (r • (ω : Space)) i *
        ((r : ℂ)^l * (((r : ℂ)*deriv η r+(l+2 : ℂ)*η r) *
          DebyeRadialTrace.angularPoloidal p (l+1) (ω : Space) i +
          ((l+1 : ℂ)*(l+2 : ℂ)*η r) * complexEvaluate p (ω : Space) *
            ((ω : Space) i : ℂ))) ∂AngularPower.angularMeasure) =
      I*z * ∫ r in Ioi (0 : ℝ), (r^2 : ℂ) * ∫ ω : AngularPower.Sphere,
      ∑ i : Fin 3, magnetic n hn z u (r • (ω : Space)) i *
        (η r * (r : ℂ)^(l+1) * DebyeRadialTrace.angularToroidal p (ω : Space) i)
        ∂AngularPower.angularMeasure := by
  have ht : (fun y j => (toroidalVectorTest T η hη hc hs p j).val y) =
      curl (radialVector (test η p)) := by
    funext y j
    change _ - _ = _
    exact (Packet04VectorTests.curl_component (radialVector (test η p)) y j).symm
  have h1 := Packet04VectorTests.vector_integrable (ball (0 : Space) T)
    (electric n hn z T u) (electric_local n hn z T u)
    (toroidalVectorTest T η hη hc hs p)
  rw [ht] at h1
  have h2 : Integrable (fun x => ∑ i : Fin 3, magnetic n hn z u x i *
      curl (radialVector (test η p)) x i) := by
    apply integrable_finset_sum
    intro i _
    have hi := WeakAnnularMoment.integrable_mul_compact _ _
      (ComplexMagneticHelmholtz.magnetic_local n hn z u i)
      (toroidalVectorTest T η hη hc hs p i).property.1.continuous
      (toroidalVectorTest T η hη hc hs p i).property.2.1
    change Integrable (fun x => magnetic n hn z u x i *
      (fun y j => (toroidalVectorTest T η hη hc hs p j).val y) x i) at hi
    rw [ht] at hi
    exact hi
  have h := actual_toroidal_test n hn z T hT u hker η hη hc hs p
  rw [ComplexPolarIntegration.integral_polar_complex _ h1,
    ComplexPolarIntegration.integral_polar_complex _ h2] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    congr 1
    funext i
    rw [Packet04RadialCurl.radial_test_curl_curl_on_ray η hη p l hp hharm r hr ω i]
  · congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    congr 1
    funext i
    rw [Packet04RadialCurl.radial_test_curl_on_ray η hη p (l+1) hp r hr ω i]

/-- Radially cut off solid-harmonic gradient as an admissible vector test. -/
def gradientVectorTest (T : ℝ) (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) (i : Fin 3) : Test (ball (0 : Space) T) := by
  have h0 : 0 ∉ tsupport η := fun h => (hs h).1.false
  refine ⟨fun x => RadialNormTest.radialNorm η x * complexEvaluate (MvPolynomial.pderiv i p) x,
    (RadialNormTest.radialNorm_smooth η hη h0).mul (complexEvaluate_regular _),
    (RadialNormTest.radialNorm_compact η hc).mul_right, ?_⟩
  intro x hx
  have hh := RadialNormTest.radialNorm_tsupport η (tsupport_mul_subset_left hx)
  simpa [Metric.mem_ball, dist_zero_right] using (hs hh).2

/-- Actual magnetic Maxwell equation tested by the cut-off solid-harmonic
  gradient, with no interface regularity assumed. -/
theorem actual_magnetic_gradient_test (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) T)
    (p : Poly) :
    (∫ x, ∑ i : Fin 3, magnetic n hn z u x i *
      curl (fun y j => η ‖y‖ * dcoord (complexEvaluate p) y j) x i) =
      -(I*z) * ∫ x, ∑ i : Fin 3, (permittivity n hn x * electric n hn z T u x i) *
        (η ‖x‖ * dcoord (complexEvaluate p) x i) := by
  have ht : (fun y j => (gradientVectorTest T η hη hc hs p j).val y) =
      fun y j => η ‖y‖ * dcoord (complexEvaluate p) y j := by
    funext y j
    simp [gradientVectorTest, RadialNormTest.radialNorm, complexEvaluate_partial, complexEvaluate]
  have h := Packet04VectorTests.weak_vector_curl (ball (0 : Space) T)
    (magnetic n hn z u) (fun x i => permittivity n hn x * electric n hn z T u x i) (-(I*z))
    (ComplexMagneticHelmholtz.magnetic_local n hn z u)
    (displacement_local n hn z T hT u hker)
    (fun i f => (actual_maxwell n hn z T hT u hker i f).2)
    (gradientVectorTest T η hη hc hs p)
  have hpt (y : Space) (j : Fin 3) := congrFun (congrFun ht y) j
  simpa only [ht, hpt] using h

#print axioms OQ14.Packet04TMProjection.gradientVectorTest
#print axioms OQ14.Packet04TMProjection.actual_magnetic_gradient_test

#print axioms OQ14.Packet04TMProjection.actual_toroidal_polar

#print axioms OQ14.Packet04TMProjection.actual_magnetic_radial_polar

#print axioms OQ14.Packet04TMProjection.displacement_local
#print axioms OQ14.Packet04TMProjection.actual_magnetic_radial_test

#print axioms OQ14.Packet04TMProjection.toroidalVectorTest
#print axioms OQ14.Packet04TMProjection.actual_toroidal_test

#print axioms OQ14.Packet04TMProjection.radialVectorTest
#print axioms OQ14.Packet04TMProjection.actual_radial_test
end OQ14.Packet04TMProjection
