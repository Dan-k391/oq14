import HelmholtzTestCalculus

/-! # Actual compact-test Green identities on an open exterior domain -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ExteriorGreen

open MeasureTheory Filter Set OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.ExteriorClassical
open scoped Topology

theorem partial_contDiff {f : Space → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => dcoord f x i) :=
  contDiff_iff_contDiffAt.mpr (fun _ => partial_smooth hf.contDiffAt i)

theorem laplacian_continuous {f : Space → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (laplacian f) := by
  unfold laplacian
  exact continuous_finset_sum _ (fun i _ =>
    (partial_contDiff (partial_contDiff hf i) i).continuous)

theorem laplacian_congr_nhds {f g : Space → ℂ} {x : Space}
    (h : f =ᶠ[𝓝 x] g) : laplacian f x = laplacian g x := by
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  have hd : (fun y => dcoord f y i) =ᶠ[𝓝 x] (fun y => dcoord g y i) := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hy
  exact congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hd.fderiv_eq

theorem zero_nhds_of_not_tsupport {f : Space → ℂ} {x : Space}
    (hx : x ∉ tsupport f) : f =ᶠ[𝓝 x] 0 := by
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
  exact Classical.byContradiction (fun hn => hy (subset_closure hn))

theorem laplacian_zero_of_not_tsupport {f : Space → ℂ} {x : Space}
    (hx : x ∉ tsupport f) : laplacian f x = 0 := by
  rw [laplacian_congr_nhds (zero_nhds_of_not_tsupport hx)]
  simp [laplacian, dcoord]

theorem smooth_localization {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (u : Space → ℂ)
    (hu : ∀ x ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u x) :
    ∃ g : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] u := by
  obtain ⟨κ, hκ⟩ := InteriorTestDensity.exists_smooth_interior hΩ hK hKΩ
  let g : Space → ℂ := fun x => κ.function x * u x
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ Ω
    · exact κ.smooth.contDiffAt.mul (hu x hx)
    · have hts : x ∉ tsupport κ.function := fun h => hx (κ.inside h)
      have he : g =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [zero_nhds_of_not_tsupport hts] with y hy
        simp [g, hy]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨g, hg, κ.compact.mul_right, ?_⟩
  intro x hx
  filter_upwards [hκ x hx] with y hy
  simp [g, hy]

theorem second_partial_green (u φ : Space → ℂ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (i : Fin 3) :
    (∫ x, dcoord (fun y => dcoord u y i) x i * φ x) =
      ∫ x, u x * dcoord (fun y => dcoord φ y i) x i := by
  rw [partial_integration_by_parts (partial_contDiff hu i |>.of_le (by simp))
    (hφ.of_le (by simp)) hc i]
  rw [partial_integration_by_parts (hu.of_le (by simp))
    (partial_contDiff hφ i |>.of_le (by simp)) (hc.fderiv_apply ℝ (basis i)) i,
    neg_neg]

theorem laplacian_green (u φ : Space → ℂ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) :
    (∫ x, laplacian u x * φ x) = ∫ x, u x * laplacian φ x := by
  have hI (i : Fin 3) : Integrable
      (fun x => dcoord (fun y => dcoord u y i) x i * φ x) :=
    partial_mul_test_integrable (partial_contDiff hu i |>.of_le (by simp))
      (hφ.of_le (by simp)) hc i
  have hJ (i : Fin 3) : Integrable
      (fun x => u x * dcoord (fun y => dcoord φ y i) x i) :=
    (hu.continuous.mul (partial_contDiff (partial_contDiff hφ i) i).continuous).integrable_of_hasCompactSupport
        ((hc.fderiv_apply ℝ (basis i)).fderiv_apply ℝ (basis i)).mul_left
  simp only [laplacian, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum _ (fun i _ => hI i),
    integral_finset_sum _ (fun i _ => hJ i)]
  exact Finset.sum_congr rfl (fun i _ => second_partial_green u φ hu hφ hc i)

theorem local_laplacian_green {Ω : Set Space} (hΩ : IsOpen Ω)
    (u φ : Space → ℂ) (hu : ∀ x ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    (∫ x, laplacian u x * φ x) = ∫ x, u x * laplacian φ x := by
  obtain ⟨g, hg, _, he⟩ := smooth_localization hΩ hc hs u hu
  have hleft : (fun x => laplacian u x * φ x) =
      (fun x => laplacian g x * φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [laplacian_congr_nhds (he x hx)]
    · simp [(zero_nhds_of_not_tsupport hx).eq_of_nhds]
  have hright : (fun x => u x * laplacian φ x) =
      (fun x => g x * laplacian φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [(he x hx).eq_of_nhds]
    · simp [laplacian_zero_of_not_tsupport hx]
  rw [hleft, hright]
  exact laplacian_green g φ hg hφ hc

theorem local_test_integrable {Ω : Set Space} (hΩ : IsOpen Ω)
    (u φ : Space → ℂ) (hu : ∀ x ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x => u x * φ x) ∧
    Integrable (fun x => u x * laplacian φ x) := by
  obtain ⟨g, hg, _, he⟩ := smooth_localization hΩ hc hs u hu
  have hprod : (fun x => u x * φ x) = (fun x => g x * φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [(he x hx).eq_of_nhds]
    · simp [(zero_nhds_of_not_tsupport hx).eq_of_nhds]
  have hlap : (fun x => u x * laplacian φ x) =
      (fun x => g x * laplacian φ x) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · rw [(he x hx).eq_of_nhds]
    · simp [laplacian_zero_of_not_tsupport hx]
  have hcompact : HasCompactSupport (laplacian φ) := by
    apply hc.of_isClosed_subset isClosed_closure
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (laplacian_zero_of_not_tsupport hn)
  rw [hprod, hlap]
  exact ⟨(hg.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left,
    (hg.continuous.mul (laplacian_continuous hφ)).integrable_of_hasCompactSupport
      hcompact.mul_left⟩

theorem local_helmholtz_test {Ω : Set Space} (hΩ : IsOpen Ω)
    (u φ : Space → ℂ) (hu : ∀ x ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u x)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) (k : ℂ)
    (heq : ∀ x ∈ Ω, laplacian u x + k^2*u x = 0) :
    (∫ x, u x * (laplacian φ x + k^2*φ x)) = 0 := by
  obtain ⟨hI, hJ⟩ := local_test_integrable hΩ u φ hu hφ hc hs
  have hK : Integrable (fun x => k^2*(u x*φ x)) := hI.const_mul _
  have he : (fun x => laplacian u x * φ x) =
      (fun x => -(k^2*(u x*φ x))) := by
    funext x
    by_cases hx : x ∈ tsupport φ
    · have hh := heq x (hs hx)
      linear_combination hh * φ x
    · simp [(zero_nhds_of_not_tsupport hx).eq_of_nhds]
  have hg := local_laplacian_green hΩ u φ hu hφ hc hs
  rw [he, integral_neg] at hg
  calc
    _ = ∫ x, u x*laplacian φ x + k^2*(u x*φ x) := by
      congr 1
      funext x
      ring
    _ = (∫ x, u x*laplacian φ x) + ∫ x, k^2*(u x*φ x) := integral_add hJ hK
    _ = 0 := by rw [← hg]; exact neg_add_cancel _

end OQ14.ExteriorGreen

#print axioms OQ14.ExteriorGreen.partial_contDiff
#print axioms OQ14.ExteriorGreen.laplacian_continuous
#print axioms OQ14.ExteriorGreen.laplacian_congr_nhds
#print axioms OQ14.ExteriorGreen.zero_nhds_of_not_tsupport
#print axioms OQ14.ExteriorGreen.laplacian_zero_of_not_tsupport
#print axioms OQ14.ExteriorGreen.smooth_localization
#print axioms OQ14.ExteriorGreen.second_partial_green
#print axioms OQ14.ExteriorGreen.laplacian_green
#print axioms OQ14.ExteriorGreen.local_laplacian_green
#print axioms OQ14.ExteriorGreen.local_test_integrable
#print axioms OQ14.ExteriorGreen.local_helmholtz_test
