import OutgoingFiniteHelmholtz
import SpatialKernelAnalytic
import HelmholtzTranslation

/-! The actual point-dyadic components satisfy the scalar Helmholtz equation off their source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace OQ14.PointDyadicHelmholtz
open Set Filter OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.DebyeCalculus
open scoped Topology

theorem partial_preserves {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℂ)
    (hf : ∀ x∈Ω,ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (heq : ∀ x∈Ω,laplacian f x+f x=0) (x : Space) (hx : x∈Ω) (i : Fin 3) :
    laplacian (fun y => dcoord f y i) x+dcoord f x i=0 := by
  rw [←partial_laplacian f x (hf x hx) i]
  have he : laplacian f =ᶠ[𝓝 x] (fun y => -1*f y) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    linear_combination heq y hy
  rw [partial_congr he,partial_const_mul ((hf x hx).differentiableAt (by simp)) (-1) i]
  ring

theorem phi_helmholtz (x : Space) (hx : x≠0) : laplacian (GreenKernel.phi 1) x+GreenKernel.phi 1 x=0 := by
  rw [laplacian_eq_divergence_gradient]
  simpa only [Complex.ofReal_one,one_pow,one_mul] using GreenKernel.phi_helmholtz 1 x hx

theorem phi_partial_helmholtz (x : Space) (hx : x≠0) (j : Fin 3) :
    laplacian (fun y => dcoord (GreenKernel.phi 1) y j) x+dcoord (GreenKernel.phi 1) x j=0 :=
  partial_preserves isOpen_compl_singleton _
    (fun y hy => (SpatialKernelAnalytic.real_phi_analyticAt 1 y hy).contDiffAt)
    phi_helmholtz x hx j

theorem phi_second_helmholtz (x : Space) (hx : x≠0) (i j : Fin 3) :
    laplacian (fun y => dcoord (fun z => dcoord (GreenKernel.phi 1) z j) y i) x+
      dcoord (fun z => dcoord (GreenKernel.phi 1) z j) x i=0 :=
  partial_preserves isOpen_compl_singleton _
    (fun y hy => ExteriorClassical.partial_smooth
      (SpatialKernelAnalytic.real_phi_analyticAt 1 y hy).contDiffAt j)
    (fun y hy => phi_partial_helmholtz y hy j) x hx i

theorem dyadic_smooth (x : Space) (hx : x≠0) (i j : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => DyadicKernel.dyadic 1 y i j) x :=
  ((contDiffAt_const.mul (SpatialKernelAnalytic.real_phi_analyticAt 1 x hx).contDiffAt).mul contDiffAt_const).add
    (SpatialKernelAnalytic.real_phiHessian_analyticAt 1 x hx i j).contDiffAt

theorem dyadic_helmholtz (x : Space) (hx : x≠0) (i j : Fin 3) :
    laplacian (fun y => DyadicKernel.dyadic 1 y i j) x+DyadicKernel.dyadic 1 x i j=0 := by
  let F := fun y => (if i=j then (1 : ℂ) else 0)*GreenKernel.phi 1 y+
    dcoord (fun z => dcoord (GreenKernel.phi 1) z j) y i
  have he : (fun y => DyadicKernel.dyadic 1 y i j)=ᶠ[𝓝 x] F := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp only [DyadicKernel.dyadic,Complex.ofReal_one,one_pow,one_mul,F,
      GreenKernel.phi_second_partial 1 y hy i j]
    ring
  rw [ExteriorGreen.laplacian_congr_nhds he,he.eq_of_nhds]
  simpa only [F,one_mul] using OutgoingFiniteHelmholtz.linear_helmholtz
    (if i=j then (1 : ℂ) else 0) 1 (GreenKernel.phi 1)
    (fun y => dcoord (fun z => dcoord (GreenKernel.phi 1) z j) y i) x
    (SpatialKernelAnalytic.real_phi_analyticAt 1 x hx).contDiffAt
    (ExteriorClassical.partial_smooth (ExteriorClassical.partial_smooth
      (SpatialKernelAnalytic.real_phi_analyticAt 1 x hx).contDiffAt j) i)
    (phi_helmholtz x hx) (phi_second_helmholtz x hx i j)

theorem translated_smooth (y x : Space) (hxy : x≠y) (i j : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => DyadicKernel.dyadic 1 (z-y) i j) x :=
  (dyadic_smooth (x-y) (sub_ne_zero.mpr hxy) i j).comp x (contDiffAt_id.sub contDiffAt_const)

theorem translated_helmholtz (y x : Space) (hxy : x≠y) (i j : Fin 3) :
    laplacian (fun z => DyadicKernel.dyadic 1 (z-y) i j) x+DyadicKernel.dyadic 1 (x-y) i j=0 := by
  have he : (fun z => DyadicKernel.dyadic 1 (z-y) i j)=
      HelmholtzTranslation.translated (-y) (fun z => DyadicKernel.dyadic 1 z i j) := by
    funext z
    simp only [HelmholtzTranslation.translated,sub_eq_add_neg,add_comm]
  rw [he,HelmholtzTranslation.translated_laplacian]
  simpa only [neg_add_eq_sub] using dyadic_helmholtz (x-y) (sub_ne_zero.mpr hxy) i j

end OQ14.PointDyadicHelmholtz


#print axioms OQ14.PointDyadicHelmholtz.partial_preserves
#print axioms OQ14.PointDyadicHelmholtz.phi_helmholtz
#print axioms OQ14.PointDyadicHelmholtz.phi_partial_helmholtz
#print axioms OQ14.PointDyadicHelmholtz.phi_second_helmholtz
#print axioms OQ14.PointDyadicHelmholtz.dyadic_smooth
#print axioms OQ14.PointDyadicHelmholtz.dyadic_helmholtz
#print axioms OQ14.PointDyadicHelmholtz.translated_smooth
#print axioms OQ14.PointDyadicHelmholtz.translated_helmholtz
