import HelmholtzInteriorKernel
import WeakPoynting.Translations
import WeakPoynting.InteriorTestDensity

/-! Actual compact-interior point evaluation bounded by the local Helmholtz L2 norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HelmholtzInteriorEstimate
open MeasureTheory Filter Set OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.WeakCurl
  OQ14.HelmholtzInteriorRepresentation OQ14.HelmholtzInteriorLocal OQ14.HelmholtzInteriorKernel
  OQ14.PartialSmoothing
open scoped Topology

theorem kernel_uniform_bound (k : ℝ) (χ : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (K : Set Space) (hK : IsCompact K)
    (hχK : ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ y, ‖kernel k χ x y‖ ≤ B := by
  have hcont : ContinuousOn (fun p : Space × Space => kernel k χ p.1 p.2)
      (K ×ˢ tsupport χ) := fun p hp =>
    (kernel_joint_smooth k χ hχ p.1 p.2 (hχK p.1 hp.1)).continuousAt.continuousWithinAt
  obtain ⟨B,hB⟩ := (hK.prod hc).exists_bound_of_continuousOn hcont
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro x hx y
  by_cases hy : y ∈ tsupport χ
  · exact (hB (x,y) ⟨hx,hy⟩).trans (le_max_left _ _)
  · rw [kernel_zero_of_not_tsupport k χ x y hy,norm_zero]
    exact le_max_right _ _

theorem kernel_uniform_L2_bound (k : ℝ) (χ : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (K : Set Space) (hK : IsCompact K)
    (hχK : ∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x (hx : x ∈ K),
      ‖continuousL2 (kernel k χ x) (kernel_row_continuous k χ hχ x (hχK x hx))
        (kernel_compact k χ hc x)‖ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := kernel_uniform_bound k χ hχ hc K hK hχK
  let z : L2Scalar := indicatorConstLp 2 hc.measurableSet (ne_of_lt hc.measure_lt_top) (1 : ℂ)
  refine ⟨B*‖z‖,mul_nonneg hB (norm_nonneg _),?_⟩
  intro x hx
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [continuousL2_ae (kernel k χ x) (kernel_row_continuous k χ hχ x (hχK x hx))
    (kernel_compact k χ hc x),indicatorConstLp_coeFn (p := (2 : ENNReal))
      (hs := hc.measurableSet) (hμs := ne_of_lt hc.measure_lt_top) (c := (1 : ℂ))] with y hy hz
  rw [hy]
  change z y=(tsupport χ).indicator (fun _ => (1 : ℂ)) y at hz
  rw [hz]
  by_cases hs : y ∈ tsupport χ
  · rw [indicator_of_mem hs,norm_one,mul_one]
    exact hbound x hx y
  · rw [indicator_of_not_mem hs,kernel_zero_of_not_tsupport k χ x y hs,norm_zero,mul_zero]

theorem compact_interior_estimate (Ω K : Set Space) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Space → ℂ) (F : L2Scalar),
      (∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u y) →
      (∀ y ∈ Ω, laplacian u y+(k : ℂ)^2*u y=0) →
      (∀ᵐ y ∂volume, y ∈ Ω → F y=u y) → ∀ x ∈ K, ‖u x‖ ≤ C*‖F‖ := by
  obtain ⟨χ,hχ⟩ := InteriorTestDensity.exists_smooth_interior hΩ hK hKΩ
  obtain ⟨C,hC,hbound⟩ := kernel_uniform_L2_bound k χ.function χ.smooth χ.compact K hK hχ
  refine ⟨C,hC,?_⟩
  intro u F hu heq hFu x hx
  let row := continuousL2 (kernel k χ.function x)
    (kernel_row_continuous k χ.function χ.smooth x (hχ x hx)) (kernel_compact k χ.function χ.compact x)
  have he : u x=WeakGreen.scalarProduct F row := by
    rw [local_representation Ω hΩ k χ.function u χ.smooth χ.compact χ.inside hu heq x
      (hχ x hx).eq_of_nhds,WeakGreen.scalarProduct_integral]
    apply integral_congr_ae
    filter_upwards [continuousL2_ae (kernel k χ.function x)
      (kernel_row_continuous k χ.function χ.smooth x (hχ x hx))
      (kernel_compact k χ.function χ.compact x),hFu] with y hy hF
    change row y=kernel k χ.function x y at hy
    rw [hy]
    by_cases hs : y ∈ tsupport χ.function
    · rw [hF (χ.inside hs)]
    · rw [kernel_zero_of_not_tsupport k χ.function x y hs]
      simp
  rw [he]
  exact (WeakTranslations.scalarProduct_norm_le F row).trans
    ((mul_le_mul_of_nonneg_left (hbound x hx) (norm_nonneg F)).trans_eq (mul_comm _ _))

end OQ14.HelmholtzInteriorEstimate
#print axioms OQ14.HelmholtzInteriorEstimate.kernel_uniform_bound
#print axioms OQ14.HelmholtzInteriorEstimate.kernel_uniform_L2_bound
#print axioms OQ14.HelmholtzInteriorEstimate.compact_interior_estimate
