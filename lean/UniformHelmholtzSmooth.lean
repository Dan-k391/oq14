import CompactTestUniformLimit
import WeakPoynting.InteriorTestDensity

/-! Uniform limits of actual local Helmholtz solutions reproduce and are smooth. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.UniformHelmholtzSmooth
open MeasureTheory Filter Set OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.ExteriorGreen
  OQ14.HelmholtzInteriorRepresentation OQ14.HelmholtzInteriorLocal OQ14.HelmholtzInteriorKernel
  OQ14.HelmholtzKernelSmoothing OQ14.CompactTestUniformLimit
open scoped Topology

theorem kernel_tsupport_subset (k : ℝ) (χ : Space → ℂ) (x : Space) :
    tsupport (kernel k χ x) ⊆ tsupport χ := by
  apply closure_minimal _ isClosed_closure
  intro y hy
  exact Classical.byContradiction (fun hn => hy (kernel_zero_of_not_tsupport k χ x y hn))

theorem limit_representation {ι : Type*} (l : Filter ι) [NeBot l]
    (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (F : ι → Space → ℂ) (u χ : Space → ℂ)
    (hF : ∀ n y, y ∈ Ω → ContDiffAt ℝ (⊤ : ℕ∞) (F n) y)
    (hEq : ∀ n y, y ∈ Ω → laplacian (F n) y+(k : ℂ)^2*F n y=0)
    (hlim : TendstoUniformlyOn F u l Ω)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ Ω)
    (x : Space) (hx : χ =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    u x=∫ y, u y*kernel k χ x y := by
  have hFc (n : ι) : ContinuousOn (F n) Ω := fun y hy => (hF n y hy).continuousAt.continuousWithinAt
  have huc := hlim.continuousOn (Eventually.of_forall hFc)
  have hxs : x ∈ tsupport χ := subset_tsupport χ (by
    change χ x≠0
    rw [hx.eq_of_nhds]
    exact one_ne_zero)
  have hks := (kernel_tsupport_subset k χ x).trans hs
  have hint := integral_mul_tendsto l Ω hΩ F u (kernel k χ x) hFc huc
    (kernel_row_continuous k χ hχ x hx) (kernel_compact k χ hc x) hks (hlim.mono hks)
  have he (n : ι) : (∫ y, F n y*kernel k χ x y)=F n x :=
    (local_representation Ω hΩ k χ (F n) hχ hc hs (hF n) (hEq n) x hx.eq_of_nhds).symm
  exact tendsto_nhds_unique (hlim.tendsto_at (hs hxs))
    (hint.congr' (Eventually.of_forall he))

theorem limit_smooth {ι : Type*} (l : Filter ι) [NeBot l]
    (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (F : ι → Space → ℂ) (u : Space → ℂ)
    (hF : ∀ n y, y ∈ Ω → ContDiffAt ℝ (⊤ : ℕ∞) (F n) y)
    (hEq : ∀ n y, y ∈ Ω → laplacian (F n) y+(k : ℂ)^2*F n y=0)
    (hlim : TendstoUniformlyOn F u l Ω) (x : Space) (hx : x ∈ Ω) :
    ContDiffAt ℝ (⊤ : ℕ∞) u x := by
  obtain ⟨χ,hχ⟩ := InteriorTestDensity.exists_smooth_interior hΩ isCompact_singleton
    (show ({x} : Set Space) ⊆ Ω from singleton_subset_iff.mpr hx)
  have hχx := hχ x (mem_singleton x)
  have huc : ContinuousOn u Ω := hlim.continuousOn (Eventually.of_forall (fun n y hy =>
    (hF n y hy).continuousAt.continuousWithinAt))
  apply (kernel_integral_smooth Ω hΩ k χ.function u χ.smooth χ.compact χ.inside huc x hχx).congr_of_eventuallyEq
  filter_upwards [hχx.eventuallyEq_nhds] with y hy
  exact limit_representation l Ω hΩ k F u χ.function hF hEq hlim χ.smooth χ.compact χ.inside y hy

end OQ14.UniformHelmholtzSmooth
#print axioms OQ14.UniformHelmholtzSmooth.kernel_tsupport_subset
#print axioms OQ14.UniformHelmholtzSmooth.limit_representation
#print axioms OQ14.UniformHelmholtzSmooth.limit_smooth
