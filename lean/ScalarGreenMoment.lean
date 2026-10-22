import LocalHelmholtzRepresentation
import SphericalMomentEquation
import HelmholtzTranslation
import AnnularMomentClassical
import AnnularMomentEquation

/-! Actual source-bearing spherical moments of the outgoing scalar Green kernel. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000

namespace OQ14.ScalarGreenMoment

open MeasureTheory Filter Set OQ14.Maxwell OQ14.GreenKernel OQ14.ExteriorHelmholtz
  OQ14.HarmonicPolynomial OQ14.SphericalMomentEquation OQ14.RadialMoment
open scoped Topology

def kernel (k : ℝ) (y x : Space) : ℂ := phi k (x-y)

def coefficient (k : ℝ) (y : Space) (p : Poly) : ℝ → ℂ :=
  moment (kernel k y) (angularPolynomial p)

theorem phi_sub_swap (k : ℝ) (x y : Space) : phi k (x-y)=phi k (y-x) := by
  exact congrArg (fun r : ℝ => radial k r/(4*Real.pi : ℂ)) (norm_sub_rev x y)

theorem test_integrable (k : ℝ) (y : Space) (φ : Space → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => kernel k y x*(laplacian φ x+(k : ℂ)^2*φ x)) := by
  have he : (fun x => kernel k y x*(laplacian φ x+(k : ℂ)^2*φ x))=
      fun x => phi k (y-x)*LocalHelmholtzRepresentation.source k φ x := by
    funext x
    rw [kernel,phi_sub_swap]
    rfl
  rw [he]
  exact LocalHelmholtzRepresentation.kernel_source_integrable k φ hφ hc y

theorem weak_source (k : ℝ) (y : Space) (φ : Space → ℂ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ x,kernel k y x*(laplacian φ x+(k : ℂ)^2*φ x))= -φ y := by
  have h := LocalHelmholtzRepresentation.compact_representation k φ hφ hc y
  have he : (fun x => kernel k y x*(laplacian φ x+(k : ℂ)^2*φ x))=
      fun x => phi k (y-x)*LocalHelmholtzRepresentation.source k φ x := by
    funext x
    rw [kernel,phi_sub_swap]
    rfl
  rw [he]
  linear_combination h

theorem weak_radial_source (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (h0 : 0 ∉ tsupport η) :
    (∫ r in Ioi (0 : ℝ),(r : ℂ)^(l+2)*coefficient k y p r*radialExpression l (k : ℂ) η r)=
      -η ‖y‖*complexEvaluate p y := by
  have hφ := test_regular η hη h0 p
  have hφc := test_compact η hc p
  have hi := test_integrable k y (test η p) hφ hφc
  have hz := weak_source k y (test η p) hφ hφc
  rw [ComplexPolarIntegration.integral_polar_complex _ hi] at hz
  have he : (∫ r in Ioi (0 : ℝ),(r : ℂ)^(l+2)*coefficient k y p r*radialExpression l (k : ℂ) η r)=
      ∫ r in Ioi (0 : ℝ),(r^2 : ℂ)*
        (∫ n : OQ14.AngularPower.Sphere,kernel k y (r • (n : Space))*
          (laplacian (test η p) (r • (n : Space))+(k : ℂ)^2*test η p (r • (n : Space)))
          ∂OQ14.AngularPower.angularMeasure) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    rw [ray_integrand (kernel k y) η hη p l hp hh (k : ℂ) r hr]
    simp only [coefficient,pow_add,pow_two]
    ring
  rw [he,hz]
  simp only [test,OQ14.RadialNormTest.radialNorm,neg_mul]

theorem weak_radial_polynomial_source (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioi (0 : ℝ)) :
    (∫ r : ℝ,(r : ℂ)^(l+2)*coefficient k y p r*deriv (deriv η) r+
      (2*(l : ℂ)+2)*(r : ℂ)^(l+1)*coefficient k y p r*deriv η r+
      (k : ℂ)^2*(r : ℂ)^(l+2)*coefficient k y p r*η r)= -η ‖y‖*complexEvaluate p y := by
  have h0 : 0 ∉ tsupport η := fun h => (lt_irrefl (0 : ℝ)) (show (0 : ℝ) < 0 from hs h)
  have hz := weak_radial_source k y p l hp hh η hη hc h0
  have he : (∫ r in Ioi (0 : ℝ),
      (r : ℂ)^(l+2)*coefficient k y p r*deriv (deriv η) r+
        (2*(l : ℂ)+2)*(r : ℂ)^(l+1)*coefficient k y p r*deriv η r+
        (k : ℂ)^2*(r : ℂ)^(l+2)*coefficient k y p r*η r)=
      ∫ r in Ioi (0 : ℝ),(r : ℂ)^(l+2)*coefficient k y p r*radialExpression l (k : ℂ) η r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    have hn : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
    simp only [radialExpression,pow_add,pow_one]
    field_simp [hn]
    ring
  have he' := he.trans hz
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at he'
  · exact he'
  · intro r hr
    have hn : r ∉ tsupport η := fun h => hr (hs h)
    have hv : η =ᶠ[𝓝 r] 0 := not_mem_tsupport_iff_eventuallyEq.mp hn
    have h1 : deriv η r=0 := by simpa only [deriv_zero] using hv.deriv_eq
    have h2 : deriv (deriv η) r=0 := by simpa only [deriv_zero] using hv.deriv.deriv_eq
    simp only [hv.eq_of_nhds,h1,h2,Pi.zero_apply,mul_zero,add_zero]

theorem kernel_contDiffAt (k : ℝ) (y x : Space) (hx : x ≠ y) :
    ContDiffAt ℝ (⊤ : ℕ∞) (kernel k y) x :=
  ((phi_contDiffAt k (x-y) (sub_ne_zero.mpr hx)).of_le (by simp)).comp x (contDiffAt_id.sub contDiffAt_const)

theorem kernel_helmholtz (k : ℝ) (y x : Space) (hx : x ≠ y) :
    laplacian (kernel k y) x+(k : ℂ)^2*kernel k y x=0 := by
  have he : kernel k y=HelmholtzTranslation.translated (-y) (phi k) := by
    funext z
    simp only [kernel,HelmholtzTranslation.translated,sub_eq_add_neg,add_comm]
  rw [he,HelmholtzTranslation.translated_laplacian]
  simp only [HelmholtzTranslation.translated,neg_add_eq_sub]
  rw [laplacian_eq_divergence_gradient]
  exact phi_helmholtz k (x-y) (sub_ne_zero.mpr hx)

theorem kernel_annular_smooth (k : ℝ) (y : Space) (R L : ℝ)
    (hy : ‖y‖ ∉ Ioo R L) :
    ContDiffOn ℝ (⊤ : ℕ∞) (kernel k y) (AnnularMoment.annulus R L) := by
  intro x hx
  apply (kernel_contDiffAt k y x ?_).contDiffWithinAt
  intro hxy
  subst x
  exact hy hx

theorem kernel_annular_helmholtz (k : ℝ) (y : Space) (R L : ℝ)
    (hy : ‖y‖ ∉ Ioo R L) :
    ∀ x ∈ AnnularMoment.annulus R L,laplacian (kernel k y) x+(k : ℂ)^2*kernel k y x=0 := by
  intro x hx
  apply kernel_helmholtz k y x
  intro hxy
  subst x
  exact hy hx

theorem coefficient_classical_annulus (k : ℝ) (y : Space) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (R L : ℝ) (hR : 0 ≤ R)
    (hy : ‖y‖ ∉ Ioo R L) :
    ∀ r ∈ Ioo R L,
      (r : ℂ)^2*momentDD (kernel k y) (angularPolynomial p) r+
        2*(r : ℂ)*momentD (kernel k y) (angularPolynomial p) r+
        ((k : ℂ)^2*(r : ℂ)^2-(l : ℂ)*((l : ℂ)+1))*coefficient k y p r=0 := by
  have hu := kernel_annular_smooth k y R L hy
  have heq := kernel_annular_helmholtz k y R L hy
  have h := AnnularMomentClassical.moment_classical_of_weak l (k : ℂ) R L hR
    (kernel k y) hu (angularPolynomial p) (angularPolynomial_continuous p)
    (fun η hη hc hs => by
      simpa only [OQ14.RadialMomentWeights.coefficientA,OQ14.RadialMomentWeights.coefficientB,
        OQ14.RadialMomentWeights.coefficientC] using
        AnnularMomentEquation.weak_radial_real_test R L hR (k : ℂ) (kernel k y) hu heq
          p l hp hh η hη hc hs)
  intro r hr
  exact (h r hr).1

end OQ14.ScalarGreenMoment

#print axioms OQ14.ScalarGreenMoment.phi_sub_swap
#print axioms OQ14.ScalarGreenMoment.test_integrable
#print axioms OQ14.ScalarGreenMoment.weak_source
#print axioms OQ14.ScalarGreenMoment.weak_radial_source
#print axioms OQ14.ScalarGreenMoment.weak_radial_polynomial_source
#print axioms OQ14.ScalarGreenMoment.kernel_contDiffAt
#print axioms OQ14.ScalarGreenMoment.kernel_helmholtz
#print axioms OQ14.ScalarGreenMoment.kernel_annular_smooth
#print axioms OQ14.ScalarGreenMoment.kernel_annular_helmholtz
#print axioms OQ14.ScalarGreenMoment.coefficient_classical_annulus
