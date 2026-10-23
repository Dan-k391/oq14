import HelmholtzInteriorRepresentation
import SpatialKernelAnalytic

/-! Genuine local Helmholtz reproduction and compact kernel support. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HelmholtzInteriorLocal
open MeasureTheory Filter Set OQ14.Maxwell OQ14.GreenKernel OQ14.ExteriorHelmholtz
  OQ14.ExteriorGreen OQ14.HelmholtzInteriorRepresentation
open scoped Topology

theorem partial_zero_of_not_tsupport (χ : Space → ℂ) (y : Space)
    (hy : y ∉ tsupport χ) (i : Fin 3) : dcoord χ y i=0 := by
  unfold dcoord
  rw [(zero_nhds_of_not_tsupport hy).fderiv_eq]
  simp

theorem kernel_zero_of_not_tsupport (k : ℝ) (χ : Space → ℂ) (x y : Space)
    (hy : y ∉ tsupport χ) : kernel k χ x y=0 := by
  simp only [kernel,laplacian_zero_of_not_tsupport hy,partial_zero_of_not_tsupport χ y hy,
    mul_zero,Finset.sum_const_zero,sub_zero]

theorem kernel_compact (k : ℝ) (χ : Space → ℂ) (hc : HasCompactSupport χ) (x : Space) :
    HasCompactSupport (kernel k χ x) := by
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closure
  intro y hy
  exact Classical.byContradiction (fun hn => hy (kernel_zero_of_not_tsupport k χ x y hn))

theorem local_representation (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (χ u : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω)
    (hu : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u y)
    (heq : ∀ y ∈ Ω, laplacian u y+(k : ℂ)^2*u y=0)
    (x : Space) (hx : χ x=1) : u x=∫ y, u y*kernel k χ x y := by
  obtain ⟨g,hg,_,he⟩ := smooth_localization hΩ hc hs u hu
  have hx' : x ∈ tsupport χ := subset_tsupport χ (by change χ x ≠ 0; rw [hx]; exact one_ne_zero)
  have hgEq (y : Space) (hy : y ∈ tsupport χ) : laplacian g y+(k : ℂ)^2*g y=0 := by
    rw [laplacian_congr_nhds (he y hy),(he y hy).eq_of_nhds]
    exact heq y (hs hy)
  rw [← (he x hx').eq_of_nhds,cutoff_representation k χ g hχ hg hc hgEq x hx]
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ tsupport χ
  · rw [(he y hy).eq_of_nhds]
  · rw [kernel_zero_of_not_tsupport k χ x y hy]
    simp

end OQ14.HelmholtzInteriorLocal
#print axioms OQ14.HelmholtzInteriorLocal.partial_zero_of_not_tsupport
#print axioms OQ14.HelmholtzInteriorLocal.kernel_zero_of_not_tsupport
#print axioms OQ14.HelmholtzInteriorLocal.kernel_compact
#print axioms OQ14.HelmholtzInteriorLocal.local_representation
