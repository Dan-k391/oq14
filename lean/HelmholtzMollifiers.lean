import WeakHelmholtzRegularity

/-! # Genuine shrinking mollifiers for the local weak Helmholtz equation

The existing normalized smooth bumps have their actual finite kernel radius.
The same actual convolutions converge almost everywhere and solve the classical
equation eventually on every fixed smaller ball. No smooth representative of the
original weak function is assumed or asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.HelmholtzMollifiers

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.WeakPoynting
  OQ14.WeakHelmholtzRegularity OQ14.ExteriorHelmholtz
open scoped Topology Convolution

theorem complexKernel_tsupport (φ : ContDiffBump (0 : Space)) :
    tsupport (complexKernel φ) = closedBall 0 φ.rOut := by
  have hs : tsupport (complexKernel φ) = tsupport (φ.normed volume) := by
    apply congrArg closure
    ext x
    exact not_congr Complex.ofReal_eq_zero
  exact hs.trans φ.tsupport_normed_eq

theorem bump_helmholtz_on_ball (k : ℂ) (c : Space) (r : ℝ) (u : Space → ℂ)
    (hu : LocallyIntegrable u) (hw : IsWeakHelmholtz k (ball c r) u)
    (φ : ContDiffBump (0 : Space)) :
    ∀ x ∈ ball c (r-φ.rOut),
      laplacian (smooth (complexKernel φ) u) x+k^2*smooth (complexKernel φ) u x = 0 := by
  apply smooth_helmholtz_on_ball k c r φ.rOut u (complexKernel φ) hu hw
    (complexKernel_regular φ) (complexKernel_compact φ)
  rw [complexKernel_tsupport]

theorem eventually_helmholtz_on_fixed_ball (k : ℂ) (c : Space) (r s : ℝ) (hs : s < r)
    (u : Space → ℂ) (hu : LocallyIntegrable u) (hw : IsWeakHelmholtz k (ball c r) u) :
    ∀ᶠ n in atTop, ∀ x ∈ ball c s,
      laplacian (smooth (complexKernel (shrinkingBump n)) u) x+
        k^2*smooth (complexKernel (shrinkingBump n)) u x = 0 := by
  have he : ∀ᶠ n in atTop, (shrinkingBump n).rOut < r-s :=
    shrinkingBump_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hs))
  filter_upwards [he] with n hn
  intro x hx
  apply bump_helmholtz_on_ball k c r u hu hw (shrinkingBump n) x
  have hd : dist x c < s := hx
  exact lt_trans hd (by linarith)

theorem smooth_complexKernel (φ : ContDiffBump (0 : Space)) (u : Space → ℂ) (x : Space) :
    smooth (complexKernel φ) u x =
      convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  rw [convolution_eq_swap]
  simp only [smooth, convolution, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.lsmul_apply, complexKernel, Complex.real_smul, mul_comm]

theorem smooth_ae_tendsto (u : Space → ℂ) (hu : LocallyIntegrable u) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smooth (complexKernel (shrinkingBump n)) u x)
      atTop (𝓝 (u x)) := by
  have hr : ∀ᶠ n in atTop, (shrinkingBump n).rOut ≤ 2*(shrinkingBump n).rIn :=
    Eventually.of_forall (fun n => by simp [shrinkingBump, div_eq_mul_inv])
  simpa only [smooth_complexKernel] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable shrinkingBump_tendsto hr hu

end OQ14.HelmholtzMollifiers

#print axioms OQ14.HelmholtzMollifiers.complexKernel_tsupport
#print axioms OQ14.HelmholtzMollifiers.bump_helmholtz_on_ball
#print axioms OQ14.HelmholtzMollifiers.eventually_helmholtz_on_fixed_ball
#print axioms OQ14.HelmholtzMollifiers.smooth_complexKernel
#print axioms OQ14.HelmholtzMollifiers.smooth_ae_tendsto
