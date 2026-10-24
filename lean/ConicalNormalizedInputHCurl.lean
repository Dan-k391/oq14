import ConicalNormalizedInputTransfer
import MaterialHCurl

/-! Regional H(curl) fields and weak Maxwell equations for the fixed and normalized input in the rounded family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ConicalNormalizedInputHCurl
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume
open scoped Topology
abbrev Space := Maxwell.Space
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex

theorem exists_regional_fields (p : Data) (a k : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) (I : ConicalEntireGauge.Incident k) :
    ∃ e h : DomainCurl.HCurl (ball (0 : Space) a),
      (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) a)]
        fun x => ConicalFixedInputTransfer.electric p a k n I x j) ∧
      (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) a)]
        fun x => ConicalFixedInputTransfer.magnetic p a k n I x j) ∧
      WeakConservation.WeakMaxwell k (fun _ => 1) (ConicalSeparatedRounding.permittivity p a n) e h := by
  let c := ConicalSeparatedRounding.material p a n
  let u := ConicalMaterialRunge.solutionOperator c k a (ConicalEntireGauge.restricted a I)
  have hE (j : Fin 3) : MemLp (fun x => ConicalFixedInputTransfer.electric p a k n I x j) 2
      (DomainCurl.regionMeasure (ball (0 : Space) a)) :=
    (SmallVolumeMaxwell.total_electric_memLp_ball c k a a u I.E
      (ConicalSeparatedRounding.common_support p a n)
      (fun i => SmallVolumeMaxwell.continuous_memLp_ball _ (I.smoothE i).continuous a) j).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hH (j : Fin 3) : MemLp (fun x => ConicalFixedInputTransfer.magnetic p a k n I x j) 2
      (DomainCurl.regionMeasure (ball (0 : Space) a)) :=
    (SmallVolumeMaxwell.total_magnetic_memLp_ball c k a a u I.H
      (ConicalSeparatedRounding.common_support p a n)
      (fun i => SmallVolumeMaxwell.continuous_memLp_ball _ (I.smoothH i).continuous a) j).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  apply MaterialHCurl.exists_regional_fields isOpen_ball k (ConicalSeparatedRounding.permittivity p a n) _ _ hE hH _
    (ConicalFixedInputTransfer.rounded_maxwell p a k ha hk n I)
  intro j
  exact MaterialHCurl.coefficient_mul_memLp _ _ (MaterialHCurl.dielectric_measurable c)
    (1+c.bound) (MaterialHCurl.dielectric_norm_bound c) _ (hE j)

theorem positive_frequency_normalized_input_rounded_hcurl_transfer (p : Data) (a b R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hR : 0 < R) (hRb : R < b) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ), 0 < k → k < δ →
      ∃ c' : ModeIndex →₀ ℂ, c'≠0 ∧
        Tendsto (FiniteMixedScaledFlux.inwardPowerK k c') atTop (𝓝 1) ∧
        Tendsto (fun n => ConicalMaterialRunge.totalOperator (ConicalSeparatedRounding.material p a n) k a
            (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c'))) atTop
          (𝓝 (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
            (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c')))) ∧
        (∀ n : ℕ, MaterialMaxwell.TestMaxwell k (ConicalSeparatedRounding.permittivity p a n)
          (ConicalFixedInputTransfer.electric p a k n (FiniteAngularHerglotz.incident k c'))
          (ConicalFixedInputTransfer.magnetic p a k n (FiniteAngularHerglotz.incident k c'))) ∧
        (∀ n : ℕ, ∃ e h : DomainCurl.HCurl (ball (0 : Space) a),
          (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) a)]
            fun x => ConicalFixedInputTransfer.electric p a k n (FiniteAngularHerglotz.incident k c') x j) ∧
          (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) a)]
            fun x => ConicalFixedInputTransfer.magnetic p a k n (FiniteAngularHerglotz.incident k c') x j) ∧
          WeakConservation.WeakMaxwell k (fun _ => 1) (ConicalSeparatedRounding.permittivity p a n) e h) ∧
        ∀ R' : ℝ, 0 < R' → R' ≤ b → ∃ i : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
          0 < (volume.restrict (ball (0 : Space) R'))
            {x | M < ‖ConicalFixedInputTransfer.electric p a k n (FiniteAngularHerglotz.incident k c') x i‖} := by
  obtain ⟨δ₀,hδ₀,hall⟩ := ConicalNormalizedInputTransfer.positive_frequency_normalized_input_rounded_transfer
    p a b R ha hai hba hR hRb hν
  have hcrpos := MaterialVolumeLimit.commonRadius_positive p.contrast a p.contrast_nonnegative
  refine ⟨min δ₀ (MaterialVolumeLimit.commonRadius p.contrast a),lt_min hδ₀ hcrpos,?_⟩
  intro k hk hkd
  obtain ⟨c',hc',hflux,hlim,hmax,hpeak⟩ := hall k hk (hkd.trans_le (min_le_left _ _))
  have hcr : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  exact ⟨c',hc',hflux,hlim,hmax,
    fun n => exists_regional_fields p a k ha n hcr (FiniteAngularHerglotz.incident k c'),hpeak⟩

end OQ14.ConicalNormalizedInputHCurl
#print axioms OQ14.ConicalNormalizedInputHCurl.exists_regional_fields
#print axioms OQ14.ConicalNormalizedInputHCurl.positive_frequency_normalized_input_rounded_hcurl_transfer
