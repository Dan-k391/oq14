import FischerDecomposition
import AngularPower
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Separation by the actual homogeneous harmonic moments

The integral against a fixed continuous complex function is a continuous real
linear functional on actual continuous real sphere tests. The proved density of
the harmonic span extends zero harmonic moments to every real test. Testing the
real and imaginary parts and using the proved full support of angular measure
then gives pointwise vanishing.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.HarmonicMomentSeparation

open MeasureTheory OQ14.AngularPower
open OQ14.HarmonicPolynomial (Poly formalLaplacian)

def momentFunctional (v : C(Sphere, ℂ)) : C(Sphere, ℝ) →L[ℝ] ℂ :=
  (L1.integralCLM (α := Sphere) (E := ℂ) (μ := angularMeasure)).comp
    ((ContinuousMap.toLp 1 angularMeasure ℝ).comp
      (((ContinuousLinearMap.mul ℝ C(Sphere, ℂ)) v).comp
        (Complex.ofRealCLM.compLeftContinuousCompact Sphere)))

theorem momentFunctional_apply (v : C(Sphere, ℂ)) (g : C(Sphere, ℝ)) :
    momentFunctional v g = ∫ n : Sphere, v n * (g n : ℂ) ∂angularMeasure := by
  change L1.integralCLM
    (ContinuousMap.toLp 1 angularMeasure ℝ
      (v * (Complex.ofRealCLM.compLeftContinuousCompact Sphere) g)) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) angularMeasure
    (v * (Complex.ofRealCLM.compLeftContinuousCompact Sphere) g)] with n hn
  exact hn

theorem annihilates_all_real_tests (v : C(Sphere, ℂ))
    (hv : ∀ (l : ℕ) (p : Poly), p.IsHomogeneous l → formalLaplacian p = 0 →
      (∫ n : Sphere, v n * (SpherePolynomial.polynomialMap p n : ℂ)
        ∂angularMeasure) = 0) :
    ∀ g : C(Sphere, ℝ), (∫ n : Sphere, v n * (g n : ℂ) ∂angularMeasure) = 0 := by
  have hs : FischerDecomposition.harmonicSpan ≤
      LinearMap.ker (momentFunctional v).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro g ⟨l,p,hp,harm,rfl⟩
    change momentFunctional v (SpherePolynomial.polynomialMap p) = 0
    rw [momentFunctional_apply]
    exact hv l p hp harm
  intro g
  rw [← momentFunctional_apply]
  exact (closure_minimal (fun f hf => hs hf)
    (isClosed_eq (momentFunctional v).continuous continuous_const))
      (FischerDecomposition.harmonicSpan_dense g)

theorem zero_of_harmonic_moments (v : Sphere → ℂ) (hv : Continuous v)
    (hm : ∀ (l : ℕ) (p : Poly), p.IsHomogeneous l → formalLaplacian p = 0 →
      (∫ n : Sphere, v n * (SpherePolynomial.polynomialMap p n : ℂ)
        ∂angularMeasure) = 0) : ∀ n, v n = 0 := by
  let vc : C(Sphere, ℂ) := ⟨v, hv⟩
  let vr : C(Sphere, ℝ) := ⟨fun n => (v n).re, Complex.continuous_re.comp hv⟩
  let vi : C(Sphere, ℝ) := ⟨fun n => (v n).im, Complex.continuous_im.comp hv⟩
  have hr := annihilates_all_real_tests vc hm vr
  have hi := annihilates_all_real_tests vc hm vi
  have hir : Integrable (fun n : Sphere => v n * (vr n : ℂ)) angularMeasure :=
    (hv.mul (Complex.continuous_ofReal.comp vr.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hii : Integrable (fun n : Sphere => v n * (vi n : ℂ)) angularMeasure :=
    (hv.mul (Complex.continuous_ofReal.comp vi.continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hr2 : (∫ n : Sphere, (v n).re^2 ∂angularMeasure) = 0 := by
    calc
      _ = ∫ n : Sphere, (v n * (vr n : ℂ)).re ∂angularMeasure := by
        congr 1
        funext n
        simp [vr, Complex.mul_re, pow_two]
      _ = (∫ n : Sphere, v n * (vr n : ℂ) ∂angularMeasure).re := integral_re hir
      _ = 0 := congrArg Complex.re hr
  have hi2 : (∫ n : Sphere, (v n).im^2 ∂angularMeasure) = 0 := by
    calc
      _ = ∫ n : Sphere, (v n * (vi n : ℂ)).im ∂angularMeasure := by
        congr 1
        funext n
        simp [vi, Complex.mul_im, pow_two]
      _ = (∫ n : Sphere, v n * (vi n : ℂ) ∂angularMeasure).im := integral_im hii
      _ = 0 := congrArg Complex.im hi
  have hcr : Continuous (fun n : Sphere => (v n).re^2) :=
    (Complex.continuous_re.comp hv).pow 2
  have hci : Continuous (fun n : Sphere => (v n).im^2) :=
    (Complex.continuous_im.comp hv).pow 2
  have hzr := SphereMeasure.continuous_zero_of_integral_zero
    (fun n : Sphere => (v n).re^2) hcr
    (hcr.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun n => sq_nonneg _) hr2
  have hzi := SphereMeasure.continuous_zero_of_integral_zero
    (fun n : Sphere => (v n).im^2) hci
    (hci.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun n => sq_nonneg _) hi2
  intro n
  apply Complex.ext
  · have h := congrFun hzr n
    simp only [Pi.zero_apply] at h
    simpa only [Complex.zero_re] using (sq_eq_zero_iff.mp h)
  · have h := congrFun hzi n
    simp only [Pi.zero_apply] at h
    simpa only [Complex.zero_im] using (sq_eq_zero_iff.mp h)

end OQ14.HarmonicMomentSeparation

#print axioms OQ14.HarmonicMomentSeparation.momentFunctional_apply
#print axioms OQ14.HarmonicMomentSeparation.annihilates_all_real_tests
#print axioms OQ14.HarmonicMomentSeparation.zero_of_harmonic_moments
