import ConicalAngularCoefficient
import Mathlib.GroupTheory.CosetCover

/-! One physical unit-power finite angular input for a finite family of distinct single-tip devices. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.ConicalFiniteDeviceInput
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume
open scoped Topology
abbrev Input := ConicalAngularCoefficient.Input

/-- Concrete geometric parameters for one centered single-tip material. -/
structure Device where
  profile : Data
  materialRadius : ℝ
  extractionRadius : ℝ
  materialRadius_nonnegative : 0 ≤ materialRadius
  extractionRadius_positive : 0 < extractionRadius
  material_inside : materialRadius < profile.cutoff.rIn
  extraction_inside : extractionRadius < materialRadius
  exponent_lt_one : profile.exponent < 1

def window (d : Device) : ℝ := Classical.choose
  (ConicalAngularCoefficient.positive_frequency_nonzero d.profile d.materialRadius d.extractionRadius
    (d.extractionRadius/2) d.materialRadius_nonnegative d.material_inside d.extraction_inside
    (half_pos d.extractionRadius_positive) (by linarith [d.extractionRadius_positive]) d.exponent_lt_one)

theorem window_positive (d : Device) : 0 < window d :=
  (Classical.choose_spec (ConicalAngularCoefficient.positive_frequency_nonzero d.profile d.materialRadius d.extractionRadius
    (d.extractionRadius/2) d.materialRadius_nonnegative d.material_inside d.extraction_inside
    (half_pos d.extractionRadius_positive) (by linarith [d.extractionRadius_positive]) d.exponent_lt_one)).1

def Functional (d : Device) (k : ℝ) (hk : 0 < k)
    (hf : |k| ≤ DynamicStaticLimit.frequencyRadius
      (ConicalSeparatedSource.material d.profile d.materialRadius) d.materialRadius) : Input →ₗ[ℂ] ℂ :=
  ConicalAngularCoefficient.coefficientLinear d.profile d.materialRadius d.extractionRadius k
    d.materialRadius_nonnegative d.extractionRadius_positive d.material_inside d.extraction_inside hk.ne' hf d.exponent_lt_one

theorem functional_nonzero (d : Device) (k : ℝ) (hk : 0 < k) (hkw : k < window d) :
    ∃ hf : |k| ≤ DynamicStaticLimit.frequencyRadius
      (ConicalSeparatedSource.material d.profile d.materialRadius) d.materialRadius,
      Functional d k hk hf≠0 :=
  (Classical.choose_spec (ConicalAngularCoefficient.positive_frequency_nonzero d.profile d.materialRadius d.extractionRadius
    (d.extractionRadius/2) d.materialRadius_nonnegative d.material_inside d.extraction_inside
    (half_pos d.extractionRadius_positive) (by linarith [d.extractionRadius_positive]) d.exponent_lt_one)).2 k hk hkw

/-- Each functional is the singular coefficient of the actual material response. The devices may differ. -/
theorem common_normalized_input {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → Device) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (hk : 0 < k), k < δ →
      ∃ hf : ∀ i, |k| ≤ DynamicStaticLimit.frequencyRadius
          (ConicalSeparatedSource.material (d i).profile (d i).materialRadius) (d i).materialRadius,
        ∃ c : Input, c≠0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK k c) atTop (𝓝 1) ∧
          ∀ i, Functional (d i) k hk (hf i) c≠0 := by
  classical
  have hw : ∀ᶠ k : ℝ in 𝓝 0, ∀ i, |k| < window (d i) :=
    Filter.eventually_all.mpr (fun i => by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (window_positive (d i))] with k hk
      simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hk)
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hw
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  have hkw (i : ι) : k < window (d i) := by
    have hm : k ∈ ball (0 : ℝ) δ := by simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hk] using hkd
    simpa only [abs_of_pos hk] using hsub hm i
  choose hf hL using fun i => functional_nonzero (d i) k hk (hkw i)
  let L (i : ι) := Functional (d i) k hk (hf i)
  have hker (i : ι) : LinearMap.ker (L i)≠⊤ := by
    intro he
    apply hL i
    apply LinearMap.ext
    intro c
    change L i c=0
    apply LinearMap.mem_ker.mp
    rw [he]
    trivial
  have hex : ∃ c : Input, ∀ i, L i c≠0 := by
    apply Classical.byContradiction
    intro hn
    push_neg at hn
    have hcovers : (⋃ i, (LinearMap.ker (L i) : Set Input))=Set.univ := by
      ext c
      simp only [mem_iUnion,LinearMap.mem_ker,mem_univ,iff_true]
      exact hn c
    obtain ⟨i,hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcovers
    exact hker i hi
  obtain ⟨c,hc⟩ := hex
  have hc0 : c≠0 := by
    intro hz
    have h := hc (Classical.arbitrary ι)
    rw [hz,map_zero] at h
    exact h rfl
  let z : ℂ := (k : ℂ)*(((Real.sqrt (FiniteMixedScaledFlux.E c))⁻¹ : ℝ) : ℂ)
  have hz : z≠0 := mul_ne_zero (by exact_mod_cast hk.ne') (by
    exact_mod_cast inv_ne_zero (Real.sqrt_pos.mpr (FiniteMixedScaledFlux.E_pos c hc0)).ne')
  have hn : FiniteMixedScaledFlux.normalizeK k c=z • c := by
    unfold FiniteMixedScaledFlux.normalizeK FiniteMixedScaledFlux.normalize
    rw [smul_smul]
  refine ⟨hf,FiniteMixedScaledFlux.normalizeK k c,
    FiniteMixedScaledFlux.normalizeK_ne_zero k hk c hc0,
    FiniteMixedScaledFlux.normalizedK_limit k hk c hc0,?_⟩
  intro i
  rw [hn,map_smul]
  exact mul_ne_zero hz (hc i)

end OQ14.ConicalFiniteDeviceInput
#print axioms OQ14.ConicalFiniteDeviceInput.window_positive
#print axioms OQ14.ConicalFiniteDeviceInput.functional_nonzero
#print axioms OQ14.ConicalFiniteDeviceInput.common_normalized_input
