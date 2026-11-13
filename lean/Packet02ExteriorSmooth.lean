import ExteriorSmooth
import ComplexSphereMaxwell

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02ExteriorSmooth
open Complex MeasureTheory Metric OQ14.Maxwell OQ14.ModalWeightedMode OQ14.ComplexGreenKernel
open OQ14.WeakCurl (next previous)

theorem gradient_contDiffAt (z : ℂ) (j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => phiGradient z y j) x := by
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => ‖y‖) x := contDiffAt_norm ℝ hx
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hn
  have hj : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => y j) x :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.contDiffAt
  have he := (contDiffAt_const (c := Complex.I * z)).mul hc |>.cexp
  have hd := ((contDiffAt_const (c := Complex.I * z)).mul (hc.inv hrc)).sub
    ((contDiffAt_const (c := (1 : ℂ))).mul ((hc.pow 2).inv (pow_ne_zero 2 hrc)))
  have hu := Complex.ofRealCLM.contDiff.contDiffAt.comp x (hj.div hn hr)
  simpa only [phiGradient, radialD, Function.comp_def, Complex.ofRealCLM_apply, div_eq_mul_inv] using
    ((he.mul hd).mul hu).mul contDiffAt_const

theorem magnetic_contDiffAt (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2)
    (x : Space) (hx : 1 < ‖x‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (ComplexSphereMaxwell.magnetic n hn z u) x := by
  apply contDiffAt_pi.mpr
  intro i
  unfold ComplexSphereMaxwell.magnetic ComplexMagneticLocal.magnetic
  apply contDiffAt_const.mul
  apply ContDiffAt.sub
  · exact ExteriorSmooth.response_contDiffAt _ _ (gradient_contDiffAt z (next i))
      (DynamicVolume.source_integrable (coefficient n hn) u 1 (coefficient_support n hn) (previous i)) 1
      (DynamicVolume.source_zero (coefficient n hn) u 1 (coefficient_support n hn) (previous i)) x hx
  · exact ExteriorSmooth.response_contDiffAt _ _ (gradient_contDiffAt z (previous i))
      (DynamicVolume.source_integrable (coefficient n hn) u 1 (coefficient_support n hn) (next i)) 1
      (DynamicVolume.source_zero (coefficient n hn) u 1 (coefficient_support n hn) (next i)) x hx

theorem magnetic_contDiffOn (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (ComplexSphereMaxwell.magnetic n hn z u) {x : Space | 1 < ‖x‖} :=
  fun x hx => (magnetic_contDiffAt n hn z u x hx).contDiffWithinAt

#print axioms OQ14.Packet02ExteriorSmooth.gradient_contDiffAt
#print axioms OQ14.Packet02ExteriorSmooth.magnetic_contDiffAt
#print axioms OQ14.Packet02ExteriorSmooth.magnetic_contDiffOn
end OQ14.Packet02ExteriorSmooth
