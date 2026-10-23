import ConicalRoundedHCurl

/-! Actual physical electric and H(curl) volume peaks of the explicit rounded material family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalRoundedHotspot
open MeasureTheory Set Metric Filter OQ14.ConicalStaticVolume
open scoped Topology
abbrev Space := Maxwell.Space

theorem physical_electric_peaks (p : Data) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ MaterialVolumeLimit.commonRadius p.contrast p.cutoff.rOut ∧
      ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ p.cutoff.rIn →
      ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
        0 < (volume.restrict (ball (0 : Space) R))
          {x | M < ‖ConicalRoundedMaxwell.electric p n k x‖} := by
  obtain ⟨δ,hδ,hb,hpeaks⟩ := ConicalRoundedPeaks.explicit_rounded_peaks p hν
  refine ⟨δ,hδ,hb,?_⟩
  intro k hk hkd R hR hRR
  obtain ⟨i,hi⟩ := hpeaks k hk hkd R hR hRR
  intro M
  filter_upwards [hi M] with n hn
  have hs : ball (0 : Space) R ⊆ closedBall (0 : Space) p.cutoff.rOut :=
    (ball_subset_ball (hRR.trans p.cutoff.rIn_lt_rOut.le)).trans ball_subset_closedBall
  have he := ae_restrict_of_ae_restrict_of_subset hs (ConicalRoundedMaxwell.field_ae p n k i)
  have hm : (volume.restrict (ball (0 : Space) R))
      {x | M < ‖NewtonL2.physicalCoordinate (ConicalRoundedPeaks.field p n k) i x‖}=
      (volume.restrict (ball (0 : Space) R)) {x | M < ‖ConicalRoundedMaxwell.electric p n k x i‖} :=
    measure_congr (he.mono (fun x hx => by
      change (M < ‖NewtonL2.physicalCoordinate (ConicalRoundedMaxwell.field p n k) i x‖)=
        (M < ‖ConicalRoundedMaxwell.electric p n k x i‖)
      rw [hx]))
  rw [hm] at hn
  exact hn.trans_le (measure_mono (fun x hx => hx.trans_le (norm_le_pi_norm _ i)))

theorem hcurl_peaks (p : Data) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ MaterialVolumeLimit.commonRadius p.contrast p.cutoff.rOut ∧
      ∀ k : ℝ, 0 < k → k < δ →
      ∃ e h : ℕ → DomainCurl.HCurl (ConicalInnerMaxwell.region p),
        (∀ n, (∀ j, ((e n).val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ConicalInnerMaxwell.region p)]
            fun x => ConicalRoundedMaxwell.electric p n k x j) ∧
          (∀ j, ((h n).val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ConicalInnerMaxwell.region p)]
            fun x => ConicalRoundedMaxwell.magnetic p n k x j) ∧
          WeakConservation.WeakMaxwell k (fun _ => 1) (ConicalRoundedPeaks.permittivity p n) (e n) (h n)) ∧
        ∀ R : ℝ, 0 < R → R ≤ p.cutoff.rIn → ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
          0 < (volume.restrict (ball (0 : Space) R))
            {x | M < ‖fun j : Fin 3 => ((e n).val.1 j : Space → ℂ) x‖} := by
  classical
  obtain ⟨δ,hδ,hb,hpeaks⟩ := physical_electric_peaks p hν
  refine ⟨δ,hδ,hb,?_⟩
  intro k hk hkd
  have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le hb).le
  have hfields (n : ℕ) := ConicalRoundedHCurl.exists_regional_fields p n k hfreq
  choose e h he hh hw using hfields
  refine ⟨e,h,fun n => ⟨he n,hh n,hw n⟩,?_⟩
  intro R hR hRR M
  filter_upwards [hpeaks k hk hkd R hR hRR M] with n hn
  have hae (j : Fin 3) : ((e n).val.1 j : Space → ℂ) =ᵐ[volume.restrict (ball (0 : Space) R)]
      fun x => ConicalRoundedMaxwell.electric p n k x j :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hRR) (he n j)
  have hm : (volume.restrict (ball (0 : Space) R))
      {x | M < ‖fun j : Fin 3 => ((e n).val.1 j : Space → ℂ) x‖}=
      (volume.restrict (ball (0 : Space) R)) {x | M < ‖ConicalRoundedMaxwell.electric p n k x‖} := by
    apply measure_congr
    filter_upwards [ae_all_iff.mpr hae] with x hx
    have heq : (fun j : Fin 3 => ((e n).val.1 j : Space → ℂ) x)=ConicalRoundedMaxwell.electric p n k x := funext hx
    change (M < ‖fun j : Fin 3 => ((e n).val.1 j : Space → ℂ) x‖)=
      (M < ‖ConicalRoundedMaxwell.electric p n k x‖)
    rw [heq]
  rwa [hm]

theorem exists_prescribed_rounded_hotspots (χ : ContDiffBump (0 : Space)) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ (p : Data) (δ : ℝ), p.cutoff=χ ∧ p.contrast=d ∧ p.threshold=t ∧
      p.exponent ∈ Ioo (0 : ℝ) 1 ∧ 0 < δ ∧
      δ ≤ MaterialVolumeLimit.commonRadius d χ.rOut ∧
      (∀ n x, ConicalRoundedPeaks.permittivity p n x ∈ Icc (1 : ℝ) (1+d)) ∧
      (∀ n x, ‖x‖ ≤ ConicalTipRounding.radius n → ConicalRoundedPeaks.permittivity p n x=1) ∧
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (ConicalRoundedPeaks.permittivity p n)
        (ball (0 : Space) (ConicalTipRounding.radius n))) ∧
      (∀ n x, x ∉ closedBall (0 : Space) χ.rOut → ConicalRoundedPeaks.permittivity p n x=1) ∧
      ∀ k : ℝ, 0 < k → k < δ →
        (∀ n, ∃ e h : DomainCurl.HCurl (ConicalInnerMaxwell.region p),
          (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ConicalInnerMaxwell.region p)]
            fun x => ConicalRoundedMaxwell.electric p n k x j) ∧
          (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ConicalInnerMaxwell.region p)]
            fun x => ConicalRoundedMaxwell.magnetic p n k x j) ∧
          WeakConservation.WeakMaxwell k (fun _ => 1) (ConicalRoundedPeaks.permittivity p n) e h) ∧
        ∀ R : ℝ, 0 < R → R ≤ χ.rIn → ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
          0 < (volume.restrict (ball (0 : Space) R))
            {x | M < ‖ConicalRoundedMaxwell.electric p n k x‖} := by
  obtain ⟨p,hχ,hd',ht',hν,_⟩ := ConicalFamily.exists_data χ d t hd ht ht1
  obtain ⟨δ,hδ,hb,hpeaks⟩ := physical_electric_peaks p hν
  refine ⟨p,δ,hχ,hd',ht',⟨p.exponent_pos,hν⟩,hδ,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hχ,hd'] using hb
  · intro n x
    simpa only [hd'] using ConicalRoundedPeaks.permittivity_bounds p n x
  · exact ConicalRoundedPeaks.permittivity_one_inner p
  · exact ConicalRoundedPeaks.permittivity_smooth_near_tip p
  · intro n x hx
    exact ConicalRoundedPeaks.permittivity_one_outside p n x (by rwa [hχ])
  · intro k hk hkd
    have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
      rw [abs_of_pos hk]
      exact (hkd.trans_le hb).le
    exact ⟨fun n => ConicalRoundedHCurl.exists_regional_fields p n k hfreq,
      fun R hR hRR M => hpeaks k hk hkd R hR (by rwa [hχ]) M⟩

end OQ14.ConicalRoundedHotspot

#print axioms OQ14.ConicalRoundedHotspot.physical_electric_peaks
#print axioms OQ14.ConicalRoundedHotspot.hcurl_peaks
#print axioms OQ14.ConicalRoundedHotspot.exists_prescribed_rounded_hotspots
