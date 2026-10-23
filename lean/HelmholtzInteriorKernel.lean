import HelmholtzInteriorLocal

/-! Joint smoothness of the actual interior reproducing kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HelmholtzInteriorKernel
open MeasureTheory Filter Set OQ14.Maxwell OQ14.GreenKernel OQ14.ExteriorHelmholtz
  OQ14.ExteriorGreen OQ14.HelmholtzInteriorRepresentation OQ14.HelmholtzInteriorLocal
open scoped Topology

theorem partial_zero_of_constant_nhds (χ : Space → ℂ) (y : Space) (c : ℂ)
    (h : χ =ᶠ[𝓝 y] (fun _ => c)) (i : Fin 3) : dcoord χ y i=0 := by
  unfold dcoord
  rw [h.fderiv_eq]
  simp

theorem laplacian_zero_of_constant_nhds (χ : Space → ℂ) (y : Space) (c : ℂ)
    (h : χ =ᶠ[𝓝 y] (fun _ => c)) : laplacian χ y=0 := by
  rw [laplacian_congr_nhds h]
  simp [laplacian,dcoord]

theorem kernel_zero_of_constant_nhds (k : ℝ) (χ : Space → ℂ) (x y : Space) (c : ℂ)
    (h : χ =ᶠ[𝓝 y] (fun _ => c)) : kernel k χ x y=0 := by
  simp only [kernel,laplacian_zero_of_constant_nhds χ y c h,
    partial_zero_of_constant_nhds χ y c h,mul_zero,Finset.sum_const_zero,sub_zero]

theorem kernel_joint_smooth (k : ℝ) (χ : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (x y : Space)
    (hx : χ =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space × Space => kernel k χ p.1 p.2) (x,y) := by
  by_cases he : x=y
  · subst y
    apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Space × Space => (0 : ℂ)) (x,x)).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually hx.eventuallyEq_nhds] with p hp
    exact kernel_zero_of_constant_nhds k χ p.1 p.2 1 hp
  · have hd : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space × Space => p.1-p.2) (x,y) :=
      contDiffAt_fst.sub contDiffAt_snd
    have hp0 : ContDiffAt ℝ (⊤ : ℕ∞) (phi k) (x-y) :=
      (SpatialKernelAnalytic.real_phi_analyticAt k (x-y) (sub_ne_zero.mpr he)).contDiffAt
    have hp : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : Space × Space => phi k (p.1-p.2)) (x,y) :=
      ContDiffAt.comp (g := GreenKernel.phi k) (f := fun p : Space × Space => p.1-p.2) (x,y) hp0 hd
    have hg (i : Fin 3) : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun p : Space × Space => phiGradient k (p.1-p.2) i) (x,y) := by
      have hg0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => phiGradient k z i) (x-y) :=
        (SpatialKernelAnalytic.real_phiGradient_analyticAt k (x-y) (sub_ne_zero.mpr he) i).contDiffAt
      exact hg0.comp (x,y) hd
    have hl : ContDiff ℝ (⊤ : ℕ∞) (laplacian χ) := by
      unfold laplacian
      exact ContDiff.sum (fun i _ => partial_contDiff (partial_contDiff hχ i) i)
    exact (hp.mul (hl.contDiffAt.comp (x,y) contDiffAt_snd)).sub
      (contDiffAt_const.mul (ContDiffAt.sum (fun i _ =>
        (hg i).mul ((partial_contDiff hχ i).contDiffAt.comp (x,y) contDiffAt_snd))))

theorem kernel_row_continuous (k : ℝ) (χ : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (x : Space)
    (hx : χ =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) : Continuous (kernel k χ x) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact ((kernel_joint_smooth k χ hχ x y hx).comp y
    (contDiffAt_const.prodMk contDiffAt_id)).continuousAt

end OQ14.HelmholtzInteriorKernel
#print axioms OQ14.HelmholtzInteriorKernel.partial_zero_of_constant_nhds
#print axioms OQ14.HelmholtzInteriorKernel.laplacian_zero_of_constant_nhds
#print axioms OQ14.HelmholtzInteriorKernel.kernel_zero_of_constant_nhds
#print axioms OQ14.HelmholtzInteriorKernel.kernel_joint_smooth
#print axioms OQ14.HelmholtzInteriorKernel.kernel_row_continuous
