import ComplexGreenKernel
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Actual spatial Green kernel analyticity away from its source -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.SpatialKernelAnalytic

open Filter OQ14.Maxwell
open scoped Topology

theorem norm_analyticAt (x : Space) (hx : x ≠ 0) :
    AnalyticAt ℝ (fun y : Space => ‖y‖) x :=
  (contDiffAt_norm ℝ hx : ContDiffAt ℝ ⊤ (fun y : Space => ‖y‖) x).analyticAt

theorem complex_phi_analyticAt (k : ℂ) (x : Space) (hx : x ≠ 0) :
    AnalyticAt ℝ (ComplexGreenKernel.phi k) x :=
  (ComplexGreenKernel.phi_contDiffAt k x hx).analyticAt

theorem dcoord_analyticAt (f : Space → ℂ) (x : Space) (hf : AnalyticAt ℝ f x) (i : Fin 3) :
    AnalyticAt ℝ (fun y => dcoord f y i) x := by
  have hc : ContDiffAt ℝ ⊤ f x := hf.contDiffAt
  have hd := hc.fderiv_right (m := ⊤) (by simp)
  change AnalyticAt ℝ (fun y => (fderiv ℝ f y) (basis i)) x
  exact (hd.clm_apply contDiffAt_const).analyticAt

theorem second_dcoord_analyticAt (f : Space → ℂ) (x : Space)
    (hf : AnalyticAt ℝ f x) (i j : Fin 3) :
    AnalyticAt ℝ (fun y => dcoord (fun z => dcoord f z j) y i) x :=
  dcoord_analyticAt _ x (dcoord_analyticAt f x hf j) i

theorem complex_phiGradient_analyticAt (k : ℂ) (x : Space) (hx : x ≠ 0) (j : Fin 3) :
    AnalyticAt ℝ (fun y => ComplexGreenKernel.phiGradient k y j) x := by
  have h := dcoord_analyticAt _ x (complex_phi_analyticAt k x hx) j
  apply h.congr
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact ComplexGreenKernel.phi_partial k y hy j

theorem complex_phiHessian_analyticAt (k : ℂ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    AnalyticAt ℝ (fun y => ComplexGreenKernel.phiHessian k y i j) x := by
  have h := second_dcoord_analyticAt _ x (complex_phi_analyticAt k x hx) i j
  apply h.congr
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact ComplexGreenKernel.phi_second_partial k y hy i j

theorem real_phi_analyticAt (k : ℝ) (x : Space) (hx : x ≠ 0) :
    AnalyticAt ℝ (GreenKernel.phi k) x := complex_phi_analyticAt (k : ℂ) x hx

theorem real_phiGradient_analyticAt (k : ℝ) (x : Space) (hx : x ≠ 0) (j : Fin 3) :
    AnalyticAt ℝ (fun y => GreenKernel.phiGradient k y j) x :=
  complex_phiGradient_analyticAt (k : ℂ) x hx j

theorem real_phiHessian_analyticAt (k : ℝ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    AnalyticAt ℝ (fun y => GreenKernel.phiHessian k y i j) x :=
  complex_phiHessian_analyticAt (k : ℂ) x hx i j

theorem complex_phi_translate_analyticAt (k : ℂ) (x y : Space) (hxy : x ≠ y) :
    AnalyticAt ℝ (fun z => ComplexGreenKernel.phi k (z-y)) x := by
  exact (complex_phi_analyticAt k (x-y) (sub_ne_zero.mpr hxy)).comp (f := fun z : Space => z-y)
    (analyticAt_id.sub analyticAt_const)

theorem complex_phiGradient_translate_analyticAt (k : ℂ) (x y : Space)
    (hxy : x ≠ y) (j : Fin 3) :
    AnalyticAt ℝ (fun z => ComplexGreenKernel.phiGradient k (z-y) j) x := by
  exact (complex_phiGradient_analyticAt k (x-y) (sub_ne_zero.mpr hxy) j).comp (f := fun z : Space => z-y)
    (analyticAt_id.sub analyticAt_const)

theorem complex_phiHessian_translate_analyticAt (k : ℂ) (x y : Space)
    (hxy : x ≠ y) (i j : Fin 3) :
    AnalyticAt ℝ (fun z => ComplexGreenKernel.phiHessian k (z-y) i j) x := by
  exact (complex_phiHessian_analyticAt k (x-y) (sub_ne_zero.mpr hxy) i j).comp (f := fun z : Space => z-y)
    (analyticAt_id.sub analyticAt_const)

end OQ14.SpatialKernelAnalytic

#print axioms OQ14.SpatialKernelAnalytic.norm_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.complex_phi_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.dcoord_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.second_dcoord_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.complex_phiGradient_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.complex_phiHessian_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.real_phi_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.real_phiGradient_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.real_phiHessian_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.complex_phi_translate_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.complex_phiGradient_translate_analyticAt
#print axioms OQ14.SpatialKernelAnalytic.complex_phiHessian_translate_analyticAt
