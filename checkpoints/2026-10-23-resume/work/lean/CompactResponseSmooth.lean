import ExteriorSmooth
import ExteriorGreen

/-! Actual convolution responses are smooth away from their compact source support. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CompactResponseSmooth
open MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.KernelConvolution OQ14.ExteriorGreen
open scoped Topology

theorem localized_kernel (q : Space → ℂ)
    (hq : ∀ z, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) q z)
    (K : Set Space) (hK : IsCompact K) (x : Space) (hx : x ∉ K) :
    ∃ g : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ᶠ z in 𝓝 x, ∀ y ∈ K, g (z-y)=q (z-y) := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl x hx
  let L := (fun p : Space × Space => p.1-p.2) '' (closedBall x (ε/2) ×ˢ K)
  have hL : IsCompact L := ((isCompact_closedBall x (ε/2)).prod hK).image
    (continuous_fst.sub continuous_snd)
  have hL0 : L ⊆ ({0} : Set Space)ᶜ := by
    rintro z ⟨⟨v,y⟩,⟨hv,hy⟩,rfl⟩ hz
    have he : v=y := sub_eq_zero.mp hz
    subst y
    have hd : dist v x ≤ ε/2 := hv
    exact hball (show v ∈ ball x ε from lt_of_le_of_lt hd (by linarith)) hy
  obtain ⟨g,hg,hgc,he⟩ := smooth_localization isClosed_singleton.isOpen_compl hL hL0 q
    (fun z hz => hq z hz)
  refine ⟨g,hg,hgc,?_⟩
  filter_upwards [ball_mem_nhds x (show 0 < ε/2 by linarith)] with z hz
  intro y hy
  exact (he (z-y) ⟨(z,y),⟨ball_subset_closedBall hz,hy⟩,rfl⟩).eq_of_nhds

theorem response_contDiffAt (q ρ : Space → ℂ)
    (hq : ∀ z, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) q z)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (x : Space) (hx : x ∉ tsupport ρ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (response q ρ) x := by
  obtain ⟨g,hg,hgc,he⟩ := localized_kernel q hq (tsupport ρ) hc x hx
  have hgs : ContDiff ℝ (⊤ : ℕ∞) (response g ρ) :=
    hgc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hρ.locallyIntegrable hg
  apply hgs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [he] with z hz
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ tsupport ρ
  · rw [hz y hy]
  · simp [image_eq_zero_of_nmem_tsupport hy]

end OQ14.CompactResponseSmooth
#print axioms OQ14.CompactResponseSmooth.localized_kernel
#print axioms OQ14.CompactResponseSmooth.response_contDiffAt
