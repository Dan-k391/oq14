import ConicalEssentialUnbounded
import ConicalFamily

/-! Actual positive-frequency weak Maxwell hotspots for every prescribed positive cap contrast. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalDynamicHotspot
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalInnerMaxwell
open scoped Topology
abbrev Space := Maxwell.Space

theorem exists_fixed_contrast_hotspot (χ : ContDiffBump (0 : Space)) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ (p : Data) (δ : ℝ), p.cutoff=χ ∧ p.contrast=d ∧ p.threshold=t ∧
      p.exponent ∈ Ioo (0 : ℝ) 1 ∧ 0 < δ ∧
      δ ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut ∧ ∀ k : ℝ, 0 < k → k < δ →
      ∃ e h : DomainCurl.HCurl (region p),
        (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (region p)] fun x => E p k x j) ∧
        (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (region p)] fun x => H p k x j) ∧
        WeakConservation.WeakMaxwell k (fun _ => 1) (ConicalCapField.permittivity d t) e h ∧
        (∀ R : ℝ, 0 < R → R ≤ χ.rIn →
          ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖E p k x‖ ≤ M) ∧
        (∀ R : ℝ, 0 < R → R ≤ χ.rIn →
          ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
            ‖fun j : Fin 3 => (e.val.1 j : Space → ℂ) x‖ ≤ M) := by
  obtain ⟨p,hχ,hd',ht',hν,_⟩ := ConicalFamily.exists_data χ d t hd ht ht1
  obtain ⟨δ,hδ,hb⟩ := ConicalEssentialUnbounded.positive_frequency_electric_not_essentially_bounded p hν
  refine ⟨p,min δ (DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut),hχ,hd',ht',
    ⟨p.exponent_pos,hν⟩,lt_min hδ (DynamicStaticLimit.frequencyRadius_positive _ _),min_le_right _ _,?_⟩
  intro k hk hkd
  have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  obtain ⟨e,h,he,hh,hw⟩ := exists_regional_fields p k hfreq
  have hphysical (R : ℝ) (hR : 0 < R) (hRR : R ≤ χ.rIn) :
      ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖E p k x‖ ≤ M :=
    hb k hk (hkd.trans_le (min_le_left _ _)) R hR (by rwa [hχ])
  have hwm : WeakConservation.WeakMaxwell k (fun _ => 1) (ConicalCapField.permittivity d t) e h := by
    simpa only [epsilon,hd',ht'] using hw
  refine ⟨e,h,he,hh,hwm,hphysical,?_⟩
  intro R hR hRR
  rintro ⟨M,hM⟩
  apply hphysical R hR hRR
  refine ⟨M,?_⟩
  have hae (j : Fin 3) : (e.val.1 j : Space → ℂ) =ᵐ[volume.restrict (ball (0 : Space) R)] fun x => E p k x j :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (show R ≤ p.cutoff.rIn by rwa [hχ])) (he j)
  filter_upwards [ae_all_iff.mpr hae,hM] with x hx hm
  have hf : (fun j : Fin 3 => (e.val.1 j : Space → ℂ) x)=E p k x := funext hx
  rwa [hf] at hm

end OQ14.ConicalDynamicHotspot

#print axioms OQ14.ConicalDynamicHotspot.exists_fixed_contrast_hotspot
