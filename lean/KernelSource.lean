import KernelGradient
import NewtonHessian

/-! # Distributional dynamic Hessian and the actual outgoing source -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.KernelSource

open MeasureTheory OQ14.Maxwell OQ14.GreenKernel
open scoped ContDiff

def difference (k : ℝ) (x : Space) : ℂ := phi k x - phi 0 x
def gradientDifference (k : ℝ) (j : Fin 3) (x : Space) : ℂ :=
  phiGradient k x j - phiGradient 0 x j
def hessianDifference (k : ℝ) (i j : Fin 3) (x : Space) : ℂ :=
  phiHessian k x i j - phiHessian 0 x i j

theorem difference_differentiableAt (k : ℝ) (x : Space) (hx : x ≠ 0) :
    DifferentiableAt ℝ (difference k) x :=
  ((phi_contDiffAt k x hx).differentiableAt (by simp)).sub
    ((phi_contDiffAt 0 x hx).differentiableAt (by simp))

theorem difference_partial (k : ℝ) (x : Space) (hx : x ≠ 0) (j : Fin 3) :
    dcoord (difference k) x j = gradientDifference k j x := by
  unfold difference
  rw [partial_sub ((phi_contDiffAt k x hx).differentiableAt (by simp))
    ((phi_contDiffAt 0 x hx).differentiableAt (by simp)), phi_partial k x hx, phi_partial 0 x hx]
  rfl

theorem gradientDifference_differentiableAt (k : ℝ) (j : Fin 3) (x : Space) (hx : x ≠ 0) :
    DifferentiableAt ℝ (gradientDifference k j) x :=
  (KernelGradient.gradient_differentiableAt k j x hx).sub
    (KernelGradient.gradient_differentiableAt 0 j x hx)

theorem gradientDifference_partial (k : ℝ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    dcoord (gradientDifference k j) x i = hessianDifference k i j x := by
  unfold gradientDifference
  rw [partial_sub (KernelGradient.gradient_differentiableAt k j x hx)
    (KernelGradient.gradient_differentiableAt 0 j x hx),
    phiGradient_partial k x hx, phiGradient_partial 0 x hx]
  rfl

theorem difference_locallyIntegrable (k : ℝ) : LocallyIntegrable (difference k) :=
  (KernelIntegrability.phi_locallyIntegrable k).sub (KernelIntegrability.phi_locallyIntegrable 0)

theorem gradientDifference_locallyIntegrable (k : ℝ) (j : Fin 3) :
    LocallyIntegrable (gradientDifference k j) :=
  (KernelGradient.gradient_locallyIntegrable k j).sub (KernelGradient.gradient_locallyIntegrable 0 j)

theorem hessianDifference_locallyIntegrable (k : ℝ) (i j : Fin 3) :
    LocallyIntegrable (hessianDifference k i j) :=
  RealKernelBounds.hessian_difference_locallyIntegrable k i j

theorem partial_contDiff {φ : Space → ℂ} (hφ : ContDiff ℝ 2 φ) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => dcoord φ x i) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ φ) :=
    (contDiff_succ_iff_fderiv (n := 1)).mp hφ |>.2.2
  exact hd.clm_apply contDiff_const

/-- The weak Hessian of phi_k-N is exactly its locally integrable pointwise
Hessian. No additional source concentrated at the origin is omitted. -/
theorem difference_weak_hessian (k : ℝ) (i j : Fin 3) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, hessianDifference k i j x * φ x) =
      ∫ x, difference k x * dcoord (fun y => dcoord φ y i) x j := by
  have hfirst := PointSingularity.weak_partial j (difference k) (gradientDifference k j)
    (difference_differentiableAt k) (fun x hx => difference_partial k x hx j)
    (difference_locallyIntegrable k) (gradientDifference_locallyIntegrable k j)
    (fun x => dcoord φ x i) (partial_contDiff hφ i) (hc.fderiv_apply ℝ (basis i))
  have hsecond := PointSingularity.weak_partial i (gradientDifference k j) (hessianDifference k i j)
    (gradientDifference_differentiableAt k j) (fun x hx => gradientDifference_partial k x hx i j)
    (gradientDifference_locallyIntegrable k j) (hessianDifference_locallyIntegrable k i j)
    φ (hφ.of_le (by norm_num)) hc
  rw [hsecond, hfirst, neg_neg]

theorem phi_test_second_integrable (k : ℝ) (i j : Fin 3) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => phi k x * dcoord (fun y => dcoord φ y i) x j) :=
  PointSingularity.test_product_integrable _ _ (KernelIntegrability.phi_locallyIntegrable k)
    (partial_continuous (partial_contDiff hφ i) j)
    ((hc.fderiv_apply ℝ (basis i)).fderiv_apply ℝ (basis j))

theorem outgoing_hessian_decomposition (k : ℝ) (i j : Fin 3) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, phi k x * dcoord (fun y => dcoord φ y i) x j) =
      (∫ x, phi 0 x * dcoord (fun y => dcoord φ y i) x j) +
        (∫ x, hessianDifference k i j x * φ x) := by
  have h := difference_weak_hessian k i j φ hφ hc
  simp only [difference, sub_mul] at h
  rw [integral_sub (phi_test_second_integrable k i j φ hφ hc)
    (phi_test_second_integrable 0 i j φ hφ hc)] at h
  exact eq_add_of_sub_eq' h.symm

theorem difference_trace (k : ℝ) (x : Space) (hx : x ≠ 0) :
    (∑ j : Fin 3, hessianDifference k j j x) = -(k : ℂ)^2 * phi k x := by
  have hk := phi_helmholtz k x hx
  have h0 := phi_helmholtz 0 x hx
  unfold divergence pd gradient at hk h0
  rw [phi_second_partial k x hx, phi_second_partial k x hx, phi_second_partial k x hx] at hk
  rw [phi_second_partial 0 x hx, phi_second_partial 0 x hx, phi_second_partial 0 x hx] at h0
  simp only [Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] at h0
  simp only [Fin.sum_univ_three, hessianDifference]
  linear_combination hk - h0

/-- The actual outgoing scalar kernel has its exact Helmholtz Dirac source.
The identity holds for every ordinary compactly supported smooth test. -/
theorem outgoing_weak_helmholtz (k : ℝ) (φ : Space → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∑ j : Fin 3, ∫ x, phi k x * dcoord (fun y => dcoord φ y j) x j) +
      (k : ℂ)^2 * (∫ x, phi k x * φ x) = -φ 0 := by
  have h2 : ContDiff ℝ 2 φ :=
    hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  let f := FourierL2.compactSmoothSchwartz φ hφ hc
  have hn := NewtonHessian.weakHessian_trace f
  change (∑ j : Fin 3, ∫ x, phi 0 x * dcoord (fun y => dcoord φ y j) x j) = -φ 0 at hn
  simp_rw [outgoing_hessian_decomposition k _ _ φ h2 hc]
  rw [Finset.sum_add_distrib, hn]
  have hi (j : Fin 3) : Integrable (fun x => hessianDifference k j j x * φ x) :=
    PointSingularity.test_product_integrable _ _ (hessianDifference_locallyIntegrable k j j)
      hφ.continuous hc
  rw [← integral_finset_sum _ (fun j _ => hi j)]
  have he : (∫ x, ∑ j : Fin 3, hessianDifference k j j x * φ x) =
      -(k : ℂ)^2 * (∫ x, phi k x * φ x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
    rw [← Finset.sum_mul, difference_trace k x hx]
    ring
  rw [he]
  ring

end OQ14.KernelSource

#print axioms OQ14.KernelSource.difference_differentiableAt
#print axioms OQ14.KernelSource.difference_partial
#print axioms OQ14.KernelSource.gradientDifference_differentiableAt
#print axioms OQ14.KernelSource.gradientDifference_partial
#print axioms OQ14.KernelSource.difference_locallyIntegrable
#print axioms OQ14.KernelSource.gradientDifference_locallyIntegrable
#print axioms OQ14.KernelSource.hessianDifference_locallyIntegrable
#print axioms OQ14.KernelSource.partial_contDiff
#print axioms OQ14.KernelSource.difference_weak_hessian
#print axioms OQ14.KernelSource.phi_test_second_integrable
#print axioms OQ14.KernelSource.outgoing_hessian_decomposition
#print axioms OQ14.KernelSource.difference_trace
#print axioms OQ14.KernelSource.outgoing_weak_helmholtz
