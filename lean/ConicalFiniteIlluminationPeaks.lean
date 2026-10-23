import ConicalSeparatedRounding
import MaterialHCurl

/-! Literal finite entire Maxwell illumination produces arbitrarily high volume superlevels in explicit tip-rounded materials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalFiniteIlluminationPeaks
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalRungeBall OQ14.ConicalRungeClosure OQ14.ConicalSeparatedRounding
open scoped Topology
abbrev Space := Maxwell.Space

def electric (p : Data) (a k : ℝ) (n : ℕ) (b : WaveIndex →₀ ℂ) : Field :=
  MaterialField.total (material p a n) k
    (ConicalMaterialRunge.solutionOperator (material p a n) k a (ConicalFinitePlanes.restricted k a b))
    (ConicalFinitePlanes.electric k b)

def magnetic (p : Data) (a k : ℝ) (n : ℕ) (b : WaveIndex →₀ ℂ) : Field :=
  MaterialMaxwell.totalMagnetic (material p a n) k
    (ConicalMaterialRunge.solutionOperator (material p a n) k a (ConicalFinitePlanes.restricted k a b))
    (ConicalFinitePlanes.magnetic k b)

theorem electric_ae (p : Data) (a k : ℝ) (n : ℕ) (b : WaveIndex →₀ ℂ) (j : Fin 3) :
    (ConicalMaterialRunge.totalOperator (material p a n) k a (ConicalFinitePlanes.restricted k a b) j : Space → ℂ)
      =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => electric p a k n b x j :=
  ConicalMaterialRunge.total_ae (material p a n) k a _ _ (common_support p a n)
    (ConicalFinitePlanes.restricted_ae k a b) j

theorem maxwell (p : Data) (a k : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) (b : WaveIndex →₀ ℂ) :
    MaterialMaxwell.TestMaxwell k (permittivity p a n) (electric p a k n b) (magnetic p a k n b) :=
  ConicalMaterialRunge.finite_solution_maxwell (material p a n) k a ha
    (hk.trans (MaterialVolumeLimit.commonRadius_le _ _ _ (by rw [material_bound]))) (common_support p a n) b

theorem exists_regional_fields (p : Data) (a k : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) (b : WaveIndex →₀ ℂ) :
    ∃ e h : DomainCurl.HCurl (ball (0 : Space) a),
      (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) a)]
        fun x => electric p a k n b x j) ∧
      (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) a)]
        fun x => magnetic p a k n b x j) ∧
      WeakConservation.WeakMaxwell k (fun _ => 1) (permittivity p a n) e h := by
  let c := material p a n
  let u := ConicalMaterialRunge.solutionOperator c k a (ConicalFinitePlanes.restricted k a b)
  have hE (j : Fin 3) : MemLp (fun x => electric p a k n b x j) 2
      (DomainCurl.regionMeasure (ball (0 : Space) a)) :=
    (SmallVolumeMaxwell.total_electric_memLp_ball c k a a u (ConicalFinitePlanes.electric k b)
      (common_support p a n) (ConicalFinitePlanes.electric_memLp_ball k a b) j).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  have hH (j : Fin 3) : MemLp (fun x => magnetic p a k n b x j) 2
      (DomainCurl.regionMeasure (ball (0 : Space) a)) :=
    (SmallVolumeMaxwell.total_magnetic_memLp_ball c k a a u (ConicalFinitePlanes.magnetic k b)
      (common_support p a n) (fun i => SmallVolumeMaxwell.continuous_memLp_ball _
        (ConicalFinitePlanes.magnetic_smooth k b i).continuous a) j).mono_measure
      (Measure.restrict_mono ball_subset_closedBall le_rfl)
  apply MaterialHCurl.exists_regional_fields isOpen_ball k (permittivity p a n) _ _ hE hH _
    (maxwell p a k ha n hk b)
  intro j
  exact MaterialHCurl.coefficient_mul_memLp _ _ (MaterialHCurl.dielectric_measurable c)
    (1+c.bound) (MaterialHCurl.dielectric_norm_bound c) _ (hE j)

theorem eventually_finite_high_superlevel (p : Data) (a k R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hk : 0 < k)
    (hfreq : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) (hRR : R ≤ a)
    (i : Fin 3) (hi : ¬∃ M : ℝ,
      ConicalBallRestriction.vector a (ConicalSeparatedDynamic.field p a k) ∈ boundedCoordinate a R M i)
    (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∃ b : WaveIndex →₀ ℂ,
      MaterialMaxwell.TestMaxwell k (permittivity p a n) (electric p a k n b) (magnetic p a k n b) ∧
      0 < (volume.restrict (ball (0 : Space) R)) {x | M < ‖electric p a k n b x‖} := by
  filter_upwards [eventually_avoids_bound p a k R ha hfreq hRR i hi M] with n hn
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp ((boundedCoordinate_isClosed a R M i hRR).isOpen_compl.mem_nhds hn)
  obtain ⟨b,hb⟩ := ConicalSeparatedIllumination.finite_total_approximation p a k ha hai hk
    (material p a n) (common_support p a n) ε hε
  have hnb : ConicalMaterialRunge.totalOperator (material p a n) k a (ConicalFinitePlanes.restricted k a b)
      ∉ boundedCoordinate a R M i := hsub (by
    change dist _ (ballField p a k n)<ε
    simpa only [dist_eq_norm,ballField] using hb)
  have hs : ball (0 : Space) R ⊆ closedBall (0 : Space) a :=
    (ball_subset_ball hRR).trans ball_subset_closedBall
  have hnE : ¬∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖electric p a k n b x i‖ ≤ M := by
    intro h
    apply hnb
    filter_upwards [h,ae_restrict_of_ae_restrict_of_subset hs (electric_ae p a k n b i)] with x hx he
    rwa [he]
  have hp : 0 < (volume.restrict (ball (0 : Space) R)) {x | M < ‖electric p a k n b x i‖} := by
    rw [ae_iff] at hnE
    exact pos_iff_ne_zero.mpr (by simpa only [not_le] using hnE)
  exact ⟨b,maxwell p a k ha n hfreq b,hp.trans_le (measure_mono (fun x hx =>
    hx.trans_le (norm_le_pi_norm _ i)))⟩

theorem positive_frequency_rounded_finite_peaks (p : Data) (a : ℝ) (ha : 0 < a)
    (hai : a < p.cutoff.rIn) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ MaterialVolumeLimit.commonRadius p.contrast a ∧
      ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ a → ∀ M : ℝ,
      ∀ᶠ n : ℕ in atTop, ∃ b : WaveIndex →₀ ℂ,
        MaterialMaxwell.TestMaxwell k (permittivity p a n) (electric p a k n b) (magnetic p a k n b) ∧
        0 < (volume.restrict (ball (0 : Space) R)) {x | M < ‖electric p a k n b x‖} := by
  obtain ⟨δ,hδ,hun⟩ := ConicalSeparatedHotspot.positive_frequency_electric_not_essentially_bounded p a ha hai hν
  refine ⟨min δ (MaterialVolumeLimit.commonRadius p.contrast a),
    lt_min hδ (MaterialVolumeLimit.commonRadius_positive _ _ p.contrast_nonnegative),min_le_right _ _,?_⟩
  intro k hk hkd R hR hRR M
  have hfreq : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  obtain ⟨i,hi⟩ := sharp_coordinate_unbounded p a k R hai hRR
    (hun k hk (hkd.trans_le (min_le_left _ _)) R hR hRR)
  exact eventually_finite_high_superlevel p a k R ha.le hai hk hfreq hRR i hi M

theorem positive_frequency_rounded_finite_hcurl_peaks (p : Data) (a : ℝ) (ha : 0 < a)
    (hai : a < p.cutoff.rIn) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ MaterialVolumeLimit.commonRadius p.contrast a ∧
      ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ a → ∀ M : ℝ,
      ∀ᶠ n : ℕ in atTop, ∃ (b : WaveIndex →₀ ℂ) (e h : DomainCurl.HCurl (ball (0 : Space) a)),
        (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) a)]
          fun x => electric p a k n b x j) ∧
        (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure (ball (0 : Space) a)]
          fun x => magnetic p a k n b x j) ∧
        WeakConservation.WeakMaxwell k (fun _ => 1) (permittivity p a n) e h ∧
        0 < (volume.restrict (ball (0 : Space) R)) {x | M < ‖electric p a k n b x‖} := by
  obtain ⟨δ,hδ,hb,hp⟩ := positive_frequency_rounded_finite_peaks p a ha hai hν
  refine ⟨δ,hδ,hb,?_⟩
  intro k hk hkd R hR hRR M
  have hfreq : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le hb).le
  filter_upwards [hp k hk hkd R hR hRR M] with n hn
  obtain ⟨b,_,hpeak⟩ := hn
  obtain ⟨e,h,he,hh,hM⟩ := exists_regional_fields p a k ha.le n hfreq b
  exact ⟨b,e,h,he,hh,hM,hpeak⟩

end OQ14.ConicalFiniteIlluminationPeaks

#print axioms OQ14.ConicalFiniteIlluminationPeaks.electric_ae
#print axioms OQ14.ConicalFiniteIlluminationPeaks.maxwell
#print axioms OQ14.ConicalFiniteIlluminationPeaks.exists_regional_fields
#print axioms OQ14.ConicalFiniteIlluminationPeaks.eventually_finite_high_superlevel
#print axioms OQ14.ConicalFiniteIlluminationPeaks.positive_frequency_rounded_finite_peaks

#print axioms OQ14.ConicalFiniteIlluminationPeaks.positive_frequency_rounded_finite_hcurl_peaks
