import SphericalMomentEquation
import HarmonicRadiationGeometry

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet04RadialCurl
open Set OQ14.Maxwell OQ14.DebyeCalculus OQ14.DebyeRadialTrace
  OQ14.HarmonicPolynomial OQ14.AngularPower
open scoped Topology

/-- The curl of the radial polynomial test, at a positive-radius sphere.
`angularToroidal` is grad(P) cross x, i.e. the negative of x cross grad(P). -/
theorem radial_test_curl_on_ray (η : ℝ → ℂ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (r : ℝ) (hr : 0 < r)
    (ω : Sphere) (i : Fin 3) :
    curl (radialVector (SphericalMomentEquation.test η p)) (r • (ω : Space)) i =
      η r * (r : ℂ)^l * angularToroidal p (ω : Space) i := by
  have hnorm : ‖r • (ω : Space)‖ = r := by
    simp [norm_smul, sphere_norm, abs_of_pos hr]
  have hx : r • (ω : Space) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hnorm]; exact hr.ne')
  change toroidal (scalar η p) (r • (ω : Space)) i = _
  rw [toroidal_components η hη.contDiffOn p _ hx, hnorm,
    HarmonicRadiationGeometry.angularToroidal_smul p l hp]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The second curl of the radial polynomial test, before splitting it into
radial and tangential surface harmonics. -/
theorem radial_test_curl_curl (η : ℝ → ℂ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p = 0)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    curl (curl (radialVector (SphericalMomentEquation.test η p))) x i =
      ((‖x‖ : ℂ)*deriv η ‖x‖+(l+1 : ℂ)*η ‖x‖)*dcoord (complexEvaluate p) x i-
        (l : ℂ)*deriv η ‖x‖/(‖x‖ : ℂ)*(x i : ℂ)*complexEvaluate p x := by
  exact toroidal_curl η hη.contDiffOn p l hp hh x hx i

/-- The curl of the toroidal test expressed using the physical radial and
surface-gradient harmonics on each positive-radius sphere. -/
theorem radial_test_curl_curl_on_ray (η : ℝ → ℂ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0)
    (r : ℝ) (hr : 0 < r) (ω : Sphere) (i : Fin 3) :
    curl (curl (radialVector (SphericalMomentEquation.test η p)))
        (r • (ω : Space)) i =
      (r : ℂ)^l * (((r : ℂ)*deriv η r+(l+2 : ℂ)*η r) *
        angularPoloidal p (l+1) (ω : Space) i +
        ((l+1 : ℂ)*(l+2 : ℂ)*η r) *
          complexEvaluate p (ω : Space) * ((ω : Space) i : ℂ)) := by
  have hnorm : ‖r • (ω : Space)‖ = r := by
    simp [norm_smul, sphere_norm, abs_of_pos hr]
  have hx : r • (ω : Space) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hnorm]; exact hr.ne')
  have hn : ‖(ω : Space)‖ = 1 := sphere_norm ω
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hg := HarmonicRadiationGeometry.homogeneous_gradient p (l+1) hp r (ω : Space) i
  rw [radial_test_curl_curl η hη p (l+1) hp hh _ hx i, hnorm,
    FischerDecomposition.complexEvaluate_smul p (l+1) hp]
  simp only [PiLp.smul_apply, Complex.ofReal_mul, angularPoloidal, hn,
    Complex.ofReal_one, one_pow, one_mul, Nat.cast_add, Nat.cast_one] at *
  rw [pow_succ] at hg
  field_simp [hr0] at *
  linear_combination ((r : ℂ)*deriv η r+((l : ℂ)+2)*η r)*hg

/-- Curl of a radial multiplier times the solid-harmonic gradient. -/
theorem curl_radial_mul_gradient (η : ℝ → ℂ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (p : Poly)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    curl (fun y j => η ‖y‖ * dcoord (complexEvaluate p) y j) x i =
      -(deriv η ‖x‖ / (‖x‖ : ℂ)) * angularToroidal p x i := by
  have hrad := (LocalRadialHarmonic.radial_smooth η hη.contDiffOn x hx).differentiableAt (by simp)
  change DifferentiableAt ℝ (fun y : Space => η ‖y‖) x at hrad
  have hpreg : ContDiffAt ℝ (⊤ : ℕ∞) (complexEvaluate p) x :=
    (complexEvaluate_regular p).contDiffAt
  have hgrad (j : Fin 3) :=
    (OQ14.ExteriorClassical.partial_smooth hpreg j).differentiableAt (by simp)
  have hc (j k : Fin 3) := OQ14.ExteriorClassical.partial_comm_at hpreg j k
  have hpartial (j : Fin 3) : dcoord (fun y : Space => η ‖y‖) x j =
      deriv η ‖x‖ * OQ14.GreenKernel.unitCoordinate j x := by
    exact LocalRadialHarmonic.radial_partial η hη.contDiffOn x hx j
  fin_cases i <;> dsimp [curl, pd, angularToroidal] <;>
    rw [partial_mul hrad (hgrad _), partial_mul hrad (hgrad _),
      hpartial, hpartial] <;>
    simp only [OQ14.GreenKernel.unitCoordinate, Complex.ofReal_div] <;>
    simp only [hc 1 2, hc 0 2, hc 0 1] <;> ring

#print axioms OQ14.Packet04RadialCurl.curl_radial_mul_gradient

#print axioms OQ14.Packet04RadialCurl.radial_test_curl_curl_on_ray

#print axioms OQ14.Packet04RadialCurl.radial_test_curl_on_ray
#print axioms OQ14.Packet04RadialCurl.radial_test_curl_curl
end OQ14.Packet04RadialCurl
