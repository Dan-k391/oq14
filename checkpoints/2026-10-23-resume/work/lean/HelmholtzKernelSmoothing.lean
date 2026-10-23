import CompactResponseSmooth
import HelmholtzInteriorKernel

/-! Smoothness of the actual reproducing integral for locally continuous data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HelmholtzKernelSmoothing
open MeasureTheory Filter Set OQ14.Maxwell OQ14.GreenKernel OQ14.ExteriorHelmholtz
  OQ14.ExteriorGreen OQ14.HelmholtzInteriorRepresentation OQ14.HelmholtzInteriorLocal
  OQ14.HelmholtzInteriorKernel OQ14.KernelConvolution
open scoped Topology

theorem partial_tsupport_subset (χ : Space → ℂ) (i : Fin 3) :
    tsupport (fun y => dcoord χ y i) ⊆ tsupport χ := by
  apply closure_minimal _ isClosed_closure
  intro y hy
  exact Classical.byContradiction (fun hn => hy (partial_zero_of_not_tsupport χ y hn i))

theorem laplacian_tsupport_subset (χ : Space → ℂ) : tsupport (laplacian χ) ⊆ tsupport χ := by
  apply closure_minimal _ isClosed_closure
  intro y hy
  exact Classical.byContradiction (fun hn => hy (laplacian_zero_of_not_tsupport hn))

theorem localized_product_continuous (Ω : Set Space) (hΩ : IsOpen Ω) (u v : Space → ℂ)
    (hu : ContinuousOn u Ω) (hv : Continuous v) (hs : tsupport v ⊆ Ω) :
    Continuous (fun y => u y*v y) :=
  (hu.mul hv.continuousOn).continuous_of_tsupport_subset hΩ (tsupport_mul_subset_right.trans hs)

theorem response_product_smooth (Ω : Set Space) (hΩ : IsOpen Ω) (u v q : Space → ℂ)
    (hu : ContinuousOn u Ω) (hv : Continuous v) (hc : HasCompactSupport v) (hs : tsupport v ⊆ Ω)
    (hq : ∀ z, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) q z) (x : Space)
    (hx : v =ᶠ[𝓝 x] (fun _ => (0 : ℂ))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (response q (fun y => u y*v y)) x := by
  have hp := localized_product_continuous Ω hΩ u v hu hv hs
  apply CompactResponseSmooth.response_contDiffAt q _ hq (hp.integrable_of_hasCompactSupport hc.mul_left)
    hc.mul_left x
  apply not_mem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [hx] with y hy
  simp only [hy,mul_zero,Pi.zero_apply]

theorem kernel_integral_split (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (χ u : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω)
    (hu : ContinuousOn u Ω) :
    (fun x => ∫ y, u y*kernel k χ x y)=fun x =>
      response (phi k) (fun y => u y*laplacian χ y) x-
        2*∑ i : Fin 3, response (fun z => phiGradient k z i) (fun y => u y*dcoord χ y i) x := by
  funext x
  have hcl : HasCompactSupport (laplacian χ) := hc.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset χ)
  have hl := localized_product_continuous Ω hΩ u (laplacian χ) hu (laplacian_continuous hχ)
    ((laplacian_tsupport_subset χ).trans hs)
  have hd (i : Fin 3) := localized_product_continuous Ω hΩ u (fun y => dcoord χ y i) hu
    (partial_contDiff hχ i).continuous ((partial_tsupport_subset χ i).trans hs)
  have hiL : Integrable (fun y => (u y*laplacian χ y)*phi k (x-y)) :=
    (translated_test_integrable (phi k) _ (KernelIntegrability.phi_locallyIntegrable k) hl hcl.mul_left x).congr
      (Eventually.of_forall (fun y => mul_comm _ _))
  have hiD (i : Fin 3) : Integrable (fun y => (u y*dcoord χ y i)*phiGradient k (x-y) i) :=
    (translated_test_integrable (fun z => phiGradient k z i) _ (KernelGradient.gradient_locallyIntegrable k i)
      (hd i) ((hc.fderiv_apply ℝ (basis i)).mul_left) x).congr (Eventually.of_forall (fun y => mul_comm _ _))
  have he : (fun y => u y*kernel k χ x y)=(fun y =>
      (u y*laplacian χ y)*phi k (x-y)-2*∑ i : Fin 3,(u y*dcoord χ y i)*phiGradient k (x-y) i) := by
    funext y
    simp only [kernel,Fin.sum_univ_three]
    ring
  rw [he,integral_sub hiL ((integrable_finset_sum _ (fun i _ => hiD i)).const_mul 2),integral_const_mul,
    integral_finset_sum (Finset.univ : Finset (Fin 3)) (f := fun i y => (u y*dcoord χ y i)*phiGradient k (x-y) i)
      (fun i _ => hiD i)]
  rfl

theorem kernel_integral_smooth (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (χ u : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω)
    (hu : ContinuousOn u Ω) (x : Space) (hx : χ =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => ∫ y, u y*kernel k χ z y) x := by
  rw [kernel_integral_split Ω hΩ k χ u hχ hc hs hu]
  apply ContDiffAt.sub
  · apply response_product_smooth Ω hΩ u (laplacian χ) (phi k) hu (laplacian_continuous hχ)
      (hc.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset χ))
      ((laplacian_tsupport_subset χ).trans hs)
      (fun z hz => (SpatialKernelAnalytic.real_phi_analyticAt k z hz).contDiffAt) x
    filter_upwards [hx.eventuallyEq_nhds] with y hy
    exact laplacian_zero_of_constant_nhds χ y 1 hy
  · apply contDiffAt_const.mul
    apply ContDiffAt.sum
    intro i _
    apply response_product_smooth Ω hΩ u (fun y => dcoord χ y i) (fun z => phiGradient k z i) hu
      (partial_contDiff hχ i).continuous (hc.fderiv_apply ℝ (basis i)) ((partial_tsupport_subset χ i).trans hs)
      (fun z hz => (SpatialKernelAnalytic.real_phiGradient_analyticAt k z hz i).contDiffAt) x
    filter_upwards [hx.eventuallyEq_nhds] with y hy
    exact partial_zero_of_constant_nhds χ y 1 hy i

end OQ14.HelmholtzKernelSmoothing
#print axioms OQ14.HelmholtzKernelSmoothing.partial_tsupport_subset
#print axioms OQ14.HelmholtzKernelSmoothing.laplacian_tsupport_subset
#print axioms OQ14.HelmholtzKernelSmoothing.localized_product_continuous
#print axioms OQ14.HelmholtzKernelSmoothing.response_product_smooth
#print axioms OQ14.HelmholtzKernelSmoothing.kernel_integral_split
#print axioms OQ14.HelmholtzKernelSmoothing.kernel_integral_smooth
