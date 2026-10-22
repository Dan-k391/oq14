import ConicalCoefficientRetention
import ConicalCorrectionBounds

/-! Actual retained conical projection cannot obey a linear radial bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalRadialUnbounded
open MeasureTheory Set Filter OQ14.ConicalStaticVolume OQ14.ConicalRadialParticular
  OQ14.ConicalCorrectionMoments OQ14.ConicalProjectedDerivative
open scoped Topology

theorem nonzero_power_not_linear_bounded (ν R : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (hR : 0 < R)
    (c : ℂ) (hc : c≠0) (P : ℝ → ℂ) (hPc : ContinuousOn P (Ioo (0 : ℝ) R))
    (L : ℝ) (hP : ∀ r ∈ Ioo (0 : ℝ) R, ‖P r‖ ≤ L*r) :
    ¬∃ M : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖c*power ν r+P r‖ ≤ M*r := by
  rintro ⟨M,hM⟩
  have hVc : ContinuousOn (fun r : ℝ => c*power ν r+P r) (Ioo (0 : ℝ) R) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp (Real.continuous_rpow_const hν.1.le))).continuousOn.add hPc
  let H : ℝ → ℝ := fun r => (‖c*power ν r+P r‖-M*r)+‖‖c*power ν r+P r‖-M*r‖
  have hXc : ContinuousOn (fun r : ℝ => ‖c*power ν r+P r‖-M*r) (Ioo (0 : ℝ) R) :=
    hVc.norm.sub ((continuous_const : Continuous (fun _ : ℝ => M)).mul continuous_id).continuousOn
  have hHc : ContinuousOn H (Ioo (0 : ℝ) R) := hXc.add hXc.norm
  have hHa : H =ᵐ[volume.restrict (Ioo (0 : ℝ) R)] (fun _ => 0) := by
    filter_upwards [hM] with r hr
    dsimp only [H]
    rw [Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hr)]
    ring
  have hHe := Measure.eqOn_open_of_ae_eq hHa isOpen_Ioo hHc continuousOn_const
  have hV (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) : ‖c*power ν r+P r‖ ≤ M*r := by
    have he := hHe hr
    change (‖c*power ν r+P r‖-M*r)+‖‖c*power ν r+P r‖-M*r‖=0 at he
    exact sub_nonpos.mp (by linarith [norm_nonneg (‖c*power ν r+P r‖-M*r)])
  have hCP (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) R) : ‖c‖*r^ν ≤ (M+L)*r := by
    calc
      _ = ‖c*power ν r‖ := by simp only [norm_mul,power,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
      _ = ‖(c*power ν r+P r)-P r‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖c*power ν r+P r‖+‖P r‖ := norm_sub_le _ _
      _ ≤ M*r+L*r := add_le_add (hV r hr) (hP r hr)
      _ = _ := by ring
  have hg := (ConicalNontrivial.singular_power_tendsto ν hν.2).eventually (eventually_gt_atTop ((M+L)/‖c‖))
  have hs₀ : ∀ᶠ r : ℝ in 𝓝 0, r<R := Iio_mem_nhds hR
  have hs : ∀ᶠ r : ℝ in 𝓝[>] 0, r<R := hs₀.filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0<r := self_mem_nhdsWithin
  obtain ⟨r,hr₀,hrR,hrg⟩ := (hpos.and (hs.and hg)).exists
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hgt : M+L < ‖c‖*r^(ν-1) := by
    simpa only [mul_comm] using (div_lt_iff₀ hcpos).mp hrg
  have hp : r^ν=r*r^(ν-1) := by
    conv_rhs => lhs; rw [← Real.rpow_one r]
    rw [← Real.rpow_add hr₀]
    congr 1
    ring
  have hh : (‖c‖*r^(ν-1))*r ≤ (M+L)*r := by
    convert hCP r ⟨hr₀,hrR⟩ using 1
    rw [hp]
    ring
  exact (not_le_of_gt hgt) ((mul_le_mul_right hr₀).mp hh)

theorem projected_not_linear_bounded (p : Data) (hν : p.exponent < 1) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (c : ℂ) (hc : c≠0)
    (he : projected p k =ᵐ[volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn)] fun r =>
      c*power p.exponent r+particular p.exponent (radialCorrection p k) (tangentCorrection p k) r) :
    ¬∃ M : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn), ‖projected p k r‖ ≤ M*r := by
  rintro ⟨M,hM⟩
  obtain ⟨C,_,hb⟩ := ConicalCorrectionBounds.particular_quadratic_bound p hν p.cutoff.rIn
  apply nonzero_power_not_linear_bounded p.exponent p.cutoff.rIn ⟨p.exponent_pos,hν⟩ p.cutoff.rIn_pos c hc
    (particular p.exponent (radialCorrection p k) (tangentCorrection p k))
    (fun r hr => (particular_hasDerivAt _ ⟨p.exponent_pos,hν⟩ _ _
      (radialCorrection_continuous p k).continuousOn (tangentCorrection_continuous p k).continuousOn r hr.1).continuousAt.continuousWithinAt)
    (k^2*C) (fun r hr => hb k hk r ⟨hr.1,hr.2.le⟩)
  refine ⟨M,?_⟩
  filter_upwards [he,hM] with r hr hm
  rwa [hr] at hm

theorem positive_frequency_projection_unbounded (p : Data) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ →
      ¬∃ M : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn), ‖projected p k r‖ ≤ M*r := by
  obtain ⟨δ,hδ,hb⟩ := ConicalCoefficientRetention.positive_frequency_nonzero_coefficient p hν
  refine ⟨min δ (DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut),
    lt_min hδ (DynamicStaticLimit.frequencyRadius_positive _ _),?_⟩
  intro k hk hkd
  obtain ⟨c,hc,he⟩ := hb k hk (hkd.trans_le (min_le_left _ _))
  have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  exact projected_not_linear_bounded p hν k hfreq c hc he

theorem projected_not_linear_bounded_on (p : Data) (hν : p.exponent < 1) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (c : ℂ) (hc : c≠0)
    (he : projected p k =ᵐ[volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn)] fun r =>
      c*power p.exponent r+particular p.exponent (radialCorrection p k) (tangentCorrection p k) r) :
    ∀ R : ℝ, 0 < R → R ≤ p.cutoff.rIn →
    ¬∃ M : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖projected p k r‖ ≤ M*r := by
  intro R hR hRR
  rintro ⟨M,hM⟩
  obtain ⟨C,_,hb⟩ := ConicalCorrectionBounds.particular_quadratic_bound p hν R
  apply nonzero_power_not_linear_bounded p.exponent R ⟨p.exponent_pos,hν⟩ hR c hc
    (particular p.exponent (radialCorrection p k) (tangentCorrection p k))
    (fun r hr => (particular_hasDerivAt _ ⟨p.exponent_pos,hν⟩ _ _
      (radialCorrection_continuous p k).continuousOn (tangentCorrection_continuous p k).continuousOn r hr.1).continuousAt.continuousWithinAt)
    (k^2*C) (fun r hr => hb k hk r ⟨hr.1,hr.2.le⟩)
  refine ⟨M,?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (show Ioo (0 : ℝ) R ⊆ Ioo (0 : ℝ) p.cutoff.rIn from fun r hr => ⟨hr.1,hr.2.trans_le hRR⟩) he,hM] with r hr hm
  rwa [hr] at hm

theorem positive_frequency_projection_unbounded_on (p : Data) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ p.cutoff.rIn →
      ¬∃ M : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖projected p k r‖ ≤ M*r := by
  obtain ⟨δ,hδ,hb⟩ := ConicalCoefficientRetention.positive_frequency_nonzero_coefficient p hν
  refine ⟨min δ (DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut),
    lt_min hδ (DynamicStaticLimit.frequencyRadius_positive _ _),?_⟩
  intro k hk hkd R hR hRR
  obtain ⟨c,hc,he⟩ := hb k hk (hkd.trans_le (min_le_left _ _))
  have hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  exact projected_not_linear_bounded_on p hν k hfreq c hc he R hR hRR

end OQ14.ConicalRadialUnbounded


#print axioms OQ14.ConicalRadialUnbounded.nonzero_power_not_linear_bounded
#print axioms OQ14.ConicalRadialUnbounded.projected_not_linear_bounded
#print axioms OQ14.ConicalRadialUnbounded.positive_frequency_projection_unbounded
#print axioms OQ14.ConicalRadialUnbounded.projected_not_linear_bounded_on
#print axioms OQ14.ConicalRadialUnbounded.positive_frequency_projection_unbounded_on
