import UniformHelmholtzSmooth
import WeakHelmholtzRegularity

/-! Uniform limits satisfy the actual weak and classical Helmholtz equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.UniformHelmholtzEquation
open MeasureTheory Filter Set OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.ExteriorGreen
  OQ14.LocalHelmholtzRepresentation OQ14.HelmholtzKernelSmoothing OQ14.CompactTestUniformLimit
  OQ14.WeakHelmholtzRegularity
open scoped Topology

theorem source_tsupport_subset (k : ℝ) (φ : Space → ℂ) : tsupport (source k φ) ⊆ tsupport φ := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  apply Classical.byContradiction
  intro hn
  apply hx
  simp only [source,laplacian_zero_of_not_tsupport hn,image_eq_zero_of_nmem_tsupport hn,mul_zero,add_zero]

theorem laplacian_smooth_at (u : Space → ℂ) (x : Space) (hu : ContDiffAt ℝ (⊤ : ℕ∞) u x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (laplacian u) x := by
  unfold laplacian
  exact ContDiffAt.sum (fun i _ => ExteriorClassical.partial_smooth (ExteriorClassical.partial_smooth hu i) i)

theorem limit_weak {ι : Type*} (l : Filter ι) [NeBot l]
    (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (F : ι → Space → ℂ) (u : Space → ℂ)
    (hF : ∀ n y, y ∈ Ω → ContDiffAt ℝ (⊤ : ℕ∞) (F n) y)
    (hEq : ∀ n y, y ∈ Ω → laplacian (F n) y+(k : ℂ)^2*F n y=0)
    (hlim : TendstoUniformlyOn F u l Ω) : IsWeakHelmholtz (k : ℂ) Ω u := by
  intro φ hφ hc hs
  have hFc (n : ι) : ContinuousOn (F n) Ω := fun y hy => (hF n y hy).continuousAt.continuousWithinAt
  have huc := hlim.continuousOn (Eventually.of_forall hFc)
  have hss := (source_tsupport_subset k φ).trans hs
  have hint := integral_mul_tendsto l Ω hΩ F u (source k φ) hFc huc
    (source_continuous k φ hφ) (source_compact k φ hc) hss (hlim.mono hss)
  have he (n : ι) : (∫ y, F n y*source k φ y)=0 :=
    local_helmholtz_test hΩ (F n) φ (hF n) hφ hc hs (k : ℂ) (hEq n)
  exact tendsto_nhds_unique hint (by simpa only [he] using (tendsto_const_nhds (x := (0 : ℂ)) (f := l)))

theorem source_test_identity (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (u φ : Space → ℂ)
    (hu : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u y)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ y, source k u y*φ y)=(∫ y, u y*source k φ y) := by
  obtain ⟨hi,hj⟩ := local_test_integrable hΩ u φ hu hφ hc hs
  have hl : Integrable (fun y => laplacian u y*φ y) :=
    (local_test_integrable hΩ (laplacian u) φ (fun y hy => laplacian_smooth_at u y (hu y hy)) hφ hc hs).1
  have heL : (fun y => source k u y*φ y)=(fun y => laplacian u y*φ y+(k : ℂ)^2*(u y*φ y)) := by
    funext y
    simp only [source]
    ring
  have heR : (fun y => u y*source k φ y)=(fun y => u y*laplacian φ y+(k : ℂ)^2*(u y*φ y)) := by
    funext y
    simp only [source]
    ring
  rw [heL,heR,integral_add hl (hi.const_mul _),integral_add hj (hi.const_mul _),
    local_laplacian_green hΩ u φ hu hφ hc hs]

theorem classical_of_weak (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (u : Space → ℂ)
    (hu : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u y) (hw : IsWeakHelmholtz (k : ℂ) Ω u) :
    ∀ y ∈ Ω, laplacian u y+(k : ℂ)^2*u y=0 := by
  have hsrc : ContinuousOn (source k u) Ω := fun y hy =>
    ((laplacian_smooth_at u y (hu y hy)).continuousAt.add
      (continuousAt_const.mul (hu y hy).continuousAt)).continuousWithinAt
  have hae : ∀ᵐ y ∂volume, y ∈ Ω → source k u y=0 :=
    hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hsrc.locallyIntegrableOn hΩ.measurableSet) (by
        intro η hη hc hs
        let φ : Space → ℂ := fun y => (η y : ℂ)
        have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := Complex.ofRealCLM.contDiff.comp hη
        have hcφ : HasCompactSupport φ := hc.comp_left (g := Complex.ofReal) (by simp)
        have hsφ : tsupport φ ⊆ Ω := by
          have he : tsupport φ=tsupport η := by
            apply congrArg closure
            ext y
            exact not_congr Complex.ofReal_eq_zero
          rwa [he]
        have ht := (source_test_identity Ω hΩ k u φ hu hφ hcφ hsφ).trans (hw φ hφ hcφ hsφ)
        simpa only [Complex.real_smul,mul_comm] using ht)
  have hae' : source k u =ᵐ[volume.restrict Ω] 0 := (ae_restrict_iff' hΩ.measurableSet).mpr hae
  exact Measure.eqOn_open_of_ae_eq hae' hΩ hsrc continuousOn_const

theorem limit_helmholtz {ι : Type*} (l : Filter ι) [NeBot l]
    (Ω : Set Space) (hΩ : IsOpen Ω) (k : ℝ) (F : ι → Space → ℂ) (u : Space → ℂ)
    (hF : ∀ n y, y ∈ Ω → ContDiffAt ℝ (⊤ : ℕ∞) (F n) y)
    (hEq : ∀ n y, y ∈ Ω → laplacian (F n) y+(k : ℂ)^2*F n y=0)
    (hlim : TendstoUniformlyOn F u l Ω) :
    (∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) u y) ∧
      (∀ y ∈ Ω, laplacian u y+(k : ℂ)^2*u y=0) := by
  have hu := UniformHelmholtzSmooth.limit_smooth l Ω hΩ k F u hF hEq hlim
  exact ⟨hu,classical_of_weak Ω hΩ k u hu (limit_weak l Ω hΩ k F u hF hEq hlim)⟩

end OQ14.UniformHelmholtzEquation
#print axioms OQ14.UniformHelmholtzEquation.source_tsupport_subset
#print axioms OQ14.UniformHelmholtzEquation.laplacian_smooth_at
#print axioms OQ14.UniformHelmholtzEquation.limit_weak
#print axioms OQ14.UniformHelmholtzEquation.source_test_identity
#print axioms OQ14.UniformHelmholtzEquation.classical_of_weak
#print axioms OQ14.UniformHelmholtzEquation.limit_helmholtz
