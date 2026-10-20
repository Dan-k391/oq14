import KernelSource
import ExteriorGreen

/-! # Actual local Helmholtz representation from the outgoing source

The outgoing fundamental solution is tested against the literal translated
reflection of a compact smooth function. Both spatial derivative signs and the
measure-preserving reflection are proved explicitly. Local smooth solutions are
then localized by an actual compact interior cutoff.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.LocalHelmholtzRepresentation

open MeasureTheory Filter Set OQ14.Maxwell OQ14.GreenKernel
  OQ14.ExteriorHelmholtz OQ14.ExteriorGreen
open scoped Topology

def reflect (x : Space) (v : Space → ℂ) (z : Space) : ℂ := v (x-z)

theorem reflect_partial (x : Space) (v : Space → ℂ)
    (hv : Differentiable ℝ v) (z : Space) (i : Fin 3) :
    dcoord (reflect x v) z i = -dcoord v (x-z) i := by
  have hd := (hv (x-z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)
  have he := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hd.fderiv
  simpa only [reflect, dcoord, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, map_neg] using he

theorem reflect_second_partial (x : Space) (v : Space → ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (z : Space) (i : Fin 3) :
    dcoord (fun y => dcoord (reflect x v) y i) z i =
      dcoord (fun y => dcoord v y i) (x-z) i := by
  have hfirst : (fun y => dcoord (reflect x v) y i) =
      fun y => -reflect x (fun w => dcoord v w i) y :=
    funext (fun y => reflect_partial x v (hv.differentiable (by simp)) y i)
  rw [hfirst]
  unfold dcoord
  rw [fderiv_neg]
  change -dcoord (reflect x (fun w => dcoord v w i)) z i = _
  rw [reflect_partial x _ ((partial_contDiff hv i).differentiable (by simp)), neg_neg]
  rfl

theorem reflect_laplacian (x : Space) (v : Space → ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (z : Space) :
    laplacian (reflect x v) z = laplacian v (x-z) := by
  simp only [laplacian, reflect_second_partial x v hv]

def source (k : ℝ) (v : Space → ℂ) (y : Space) : ℂ :=
  laplacian v y + (k : ℂ)^2*v y

theorem source_continuous (k : ℝ) (v : Space → ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) : Continuous (source k v) :=
  (laplacian_continuous hv).add (continuous_const.mul hv.continuous)

theorem source_compact (k : ℝ) (v : Space → ℂ) (hc : HasCompactSupport v) :
    HasCompactSupport (source k v) := by
  have hl : HasCompactSupport (laplacian v) := by
    apply hc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closure
    intro y hy
    by_contra hn
    exact hy (laplacian_zero_of_not_tsupport hn)
  exact hl.add hc.mul_left

theorem kernel_source_integrable (k : ℝ) (v : Space → ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hc : HasCompactSupport v) (x : Space) :
    Integrable (fun y => phi k (x-y)*source k v y) := by
  have hi : Integrable (fun z => phi k z*source k v (x-z)) :=
    PointSingularity.test_product_integrable _ _
      (KernelIntegrability.phi_locallyIntegrable k)
      ((source_continuous k v hv).comp (continuous_const.sub continuous_id))
      ((source_compact k v hc).comp_homeomorph (Homeomorph.subLeft x))
  simpa only [sub_sub_self] using hi.comp_sub_left x

theorem compact_representation (k : ℝ) (v : Space → ℂ)
    (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hc : HasCompactSupport v) (x : Space) :
    v x = -(∫ y, phi k (x-y)*source k v y) := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (reflect x v) :=
    hv.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (reflect x v) := hc.comp_homeomorph (Homeomorph.subLeft x)
  have h2 : ContDiff ℝ 2 (reflect x v) :=
    hφ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hi (j : Fin 3) : Integrable (fun z =>
      phi k z*dcoord (fun y => dcoord (reflect x v) y j) z j) :=
    KernelSource.phi_test_second_integrable k j j (reflect x v) h2 hφc
  have hj : Integrable (fun z => phi k z*reflect x v z) :=
    PointSingularity.test_product_integrable _ _
      (KernelIntegrability.phi_locallyIntegrable k) hφ.continuous hφc
  have hs : (∫ z, phi k z*source k v (x-z)) = -v x := by
    have he : (fun z => phi k z*source k v (x-z)) = fun z =>
        (∑ j : Fin 3, phi k z*dcoord (fun y => dcoord (reflect x v) y j) z j) +
          (k : ℂ)^2*(phi k z*reflect x v z) := by
      funext z
      unfold source
      rw [← reflect_laplacian x v hv z]
      simp only [laplacian, mul_add, Finset.mul_sum, reflect]
      ring
    rw [he, integral_add (integrable_finset_sum _ (fun j _ => hi j))
      (hj.const_mul _), integral_finset_sum _ (fun j _ => hi j), integral_const_mul]
    simpa only [reflect, sub_zero] using
      KernelSource.outgoing_weak_helmholtz k (reflect x v) hφ hφc
  have ht := integral_sub_left_eq_self
    (fun z => phi k z*source k v (x-z)) volume x
  have hf : (∫ y, phi k (x-y)*source k v y) = -v x := by
    simpa only [sub_sub_self] using ht.trans hs
  linear_combination hf

theorem source_congr_nhds (k : ℝ) {v u : Space → ℂ} {y : Space}
    (h : v =ᶠ[𝓝 y] u) : source k v y = source k u y := by
  rw [source, source, laplacian_congr_nhds h, h.eq_of_nhds]

theorem cutoff_source_zero (k : ℝ) (κ u : Space → ℂ) (y : Space)
    (hκ : κ =ᶠ[𝓝 y] (fun _ => 1))
    (heq : laplacian u y + (k : ℂ)^2*u y = 0) :
    source k (fun z => κ z*u z) y = 0 := by
  have he : (fun z => κ z*u z) =ᶠ[𝓝 y] u := by
    filter_upwards [hκ] with z hz
    simp only [hz, one_mul]
  rw [source_congr_nhds k he]
  exact heq

theorem local_representation {Ω K : Set Space} (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) (k : ℝ) (u : Space → ℂ)
    (hu : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u y)
    (heq : ∀ y ∈ Ω, laplacian u y + (k : ℂ)^2*u y = 0) :
    ∃ v : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) v ∧ HasCompactSupport v ∧
      (∀ y ∈ K, v =ᶠ[𝓝 y] u) ∧ (∀ y ∈ K, source k v y = 0) ∧
      ∀ x ∈ K, u x = -(∫ y, phi k (x-y)*source k v y) := by
  obtain ⟨v,hv,hvc,he⟩ := smooth_localization hΩ hK hKΩ u hu
  refine ⟨v,hv,hvc,he,?_,?_⟩
  · intro y hy
    rw [source_congr_nhds k (he y hy)]
    exact heq y (hKΩ hy)
  · intro x hx
    calc
      u x = v x := (he x hx).eq_of_nhds.symm
      _ = _ := compact_representation k v hv hvc x

end OQ14.LocalHelmholtzRepresentation

#print axioms OQ14.LocalHelmholtzRepresentation.reflect_partial
#print axioms OQ14.LocalHelmholtzRepresentation.reflect_second_partial
#print axioms OQ14.LocalHelmholtzRepresentation.reflect_laplacian
#print axioms OQ14.LocalHelmholtzRepresentation.source_continuous
#print axioms OQ14.LocalHelmholtzRepresentation.source_compact
#print axioms OQ14.LocalHelmholtzRepresentation.kernel_source_integrable
#print axioms OQ14.LocalHelmholtzRepresentation.compact_representation
#print axioms OQ14.LocalHelmholtzRepresentation.source_congr_nhds
#print axioms OQ14.LocalHelmholtzRepresentation.cutoff_source_zero
#print axioms OQ14.LocalHelmholtzRepresentation.local_representation
