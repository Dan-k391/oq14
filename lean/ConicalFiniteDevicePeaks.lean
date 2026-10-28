import ConicalFiniteDeviceInput

/-! The same normalized physical input drives high rounded superlevels in each distinct device. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.ConicalFiniteDevicePeaks
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalProjectionData
open OQ14.ConicalFiniteDeviceInput
open scoped Topology
abbrev Space := Maxwell.Space

theorem unbounded (d : Device) (k : ℝ) (hk : 0 < k)
    (hf : |k| ≤ DynamicStaticLimit.frequencyRadius
      (ConicalSeparatedSource.material d.profile d.materialRadius) d.materialRadius)
    (c : Input) (hc : Functional d k hk hf c≠0) (R : ℝ)
    (hR : 0 < R) (hRb : R ≤ d.extractionRadius) :
    ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
      ‖ConicalEntireGauge.electric d.profile d.materialRadius k (FiniteAngularHerglotz.incident k c) x‖ ≤ M := by
  let s := ConicalAngularCoefficient.system d.profile d.materialRadius d.extractionRadius k
    d.materialRadius_nonnegative d.material_inside d.extraction_inside hk.ne' hf c
  have he := ConicalIntrinsicCoefficient.coefficient_spec s d.extractionRadius_positive
    (d.extraction_inside.trans d.material_inside) d.exponent_lt_one
  exact ConicalFixedInputTransfer.fixed_input_electric_not_essentially_bounded d.profile
    d.materialRadius d.extractionRadius k d.materialRadius_nonnegative d.material_inside d.extraction_inside
    d.exponent_lt_one hk.ne' hf (FiniteAngularHerglotz.incident k c)
    (ConicalAngularCoefficient.extension d.profile d.materialRadius d.extractionRadius k d.material_inside d.extraction_inside c)
    (ConicalAngularCoefficient.extension_continuous d.profile d.materialRadius d.extractionRadius k d.material_inside d.extraction_inside c)
    (ConicalAngularCoefficient.extension_eq d.profile d.materialRadius d.extractionRadius k d.material_inside d.extraction_inside c)
    (Functional d k hk hf c) hc he R hR hRb

/-- Distinct materials, one fixed physical input, and a common sufficiently advanced rounding index. -/
theorem common_rounded_superlevels {ι : Type*} [Fintype ι] [Nonempty ι] (d : ι → Device) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ →
      ∃ c : Input, c≠0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK k c) atTop (𝓝 1) ∧
        (∀ i n, MaterialMaxwell.TestMaxwell k (ConicalSeparatedRounding.permittivity (d i).profile (d i).materialRadius n)
          (ConicalFixedInputTransfer.electric (d i).profile (d i).materialRadius k n (FiniteAngularHerglotz.incident k c))
          (ConicalFixedInputTransfer.magnetic (d i).profile (d i).materialRadius k n (FiniteAngularHerglotz.incident k c))) ∧
        ∀ R : ι → ℝ, (∀ i, 0 < R i ∧ R i ≤ (d i).extractionRadius) →
          ∃ j : ι → Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop, ∀ i,
            0 < (volume.restrict (ball (0 : Space) (R i))) {x |
              M < ‖ConicalFixedInputTransfer.electric (d i).profile (d i).materialRadius k n
                (FiniteAngularHerglotz.incident k c) x (j i)‖} := by
  classical
  obtain ⟨δ₀,hδ₀,hcommon⟩ := common_normalized_input d
  have hw : ∀ᶠ k : ℝ in 𝓝 0, ∀ i, |k| < MaterialVolumeLimit.commonRadius (d i).profile.contrast (d i).materialRadius :=
    Filter.eventually_all.mpr (fun i => by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
        (MaterialVolumeLimit.commonRadius_positive (d i).profile.contrast (d i).materialRadius (d i).profile.contrast_nonnegative)]
        with k hk
      simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs] using hk)
  obtain ⟨δ₁,hδ₁,hsub⟩ := Metric.mem_nhds_iff.mp hw
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro k hk hkd
  obtain ⟨hf,c,hc,hpower,hcoeff⟩ := hcommon k hk (hkd.trans_le (min_le_left _ _))
  have hcr (i : ι) : |k| ≤ MaterialVolumeLimit.commonRadius (d i).profile.contrast (d i).materialRadius := by
    apply (hsub (show k ∈ ball (0 : ℝ) δ₁ from by
      simpa only [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hk] using hkd.trans_le (min_le_right _ _)) i).le
  refine ⟨c,hc,hpower,fun i n => ConicalFixedInputTransfer.rounded_maxwell (d i).profile (d i).materialRadius k
    (d i).materialRadius_nonnegative (hcr i) n (FiniteAngularHerglotz.incident k c),?_⟩
  intro R hR
  have hi (i : ι) := ConicalVolumePeaks.coordinate_unbounded
    (ConicalEntireGauge.electric (d i).profile (d i).materialRadius k (FiniteAngularHerglotz.incident k c))
    (ball (0 : Space) (R i))
    (unbounded (d i) k hk (hf i) c (hcoeff i) (R i) (hR i).1 (hR i).2)
  choose j hj using hi
  refine ⟨j,?_⟩
  intro M
  exact Filter.eventually_all.mpr (fun i => ConicalFixedInputTransfer.eventually_high_superlevel (d i).profile
    (d i).materialRadius k (R i) (d i).materialRadius_nonnegative ((hR i).2.trans (d i).extraction_inside.le)
    (hcr i) (FiniteAngularHerglotz.incident k c) (j i) (hj i) M)

end OQ14.ConicalFiniteDevicePeaks
#print axioms OQ14.ConicalFiniteDevicePeaks.unbounded
#print axioms OQ14.ConicalFiniteDevicePeaks.common_rounded_superlevels
