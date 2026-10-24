import ConicalNormalizedInputHCurl
import ConicalLocalFlux
import ConicalLocalExpansion
import PolarMomentAE

/-! The singular conical coefficient of a scaled incident field is the scaled coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ConicalNormalizedInputCoefficient
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalProjectionData OQ14.ConicalRadialParticular OQ14.ConicalGraphProjection OQ14.PolarMomentTesting
open scoped Topology
abbrev Space := Maxwell.Space
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex

theorem tangentTotal_scaled (p : Data) (b : ℝ) (s s' : System p b) (z : ℂ)
    (htot : ∀ i : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate s' i x=z*totalCoordinate s i x) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) b),
      ConicalLocalFlux.tangentTotal s' r=z*ConicalLocalFlux.tangentTotal s r := by
  have hi (i : Fin 3) : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) b),
      moment (totalCoordinate s' i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r=
        z*moment (totalCoordinate s i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r := by
    have hp := PolarMomentAE.polar_ae (htot i)
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioi_self hp,
      ae_restrict_mem measurableSet_Ioo] with r hr hm
    unfold moment
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hr] with n hn
    have hx : r • (n : Space) ∈ ball (0 : Space) b := by
      simpa only [mem_ball,dist_zero_right,norm_smul,sphere_norm,Real.norm_eq_abs,abs_of_pos hm.1,mul_one]
        using hm.2
    rw [hn hx]
    ring
  filter_upwards [ae_all_iff.mpr hi] with r hr
  simp only [ConicalLocalFlux.tangentTotal,hr,Finset.mul_sum]

theorem tangent_bound (p : Data) (b : ℝ) (s : System p b) (R : ℝ) :
    ∃ C : ℝ, ∀ r ∈ Icc (0 : ℝ) R, ‖tangentCorrection s r‖ ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    (tangentCorrection_continuous s).continuousOn
  exact ⟨C,hC⟩

theorem particular_bound (p : Data) (b : ℝ) (hν : p.exponent < 1) (s : System p b) (R : ℝ) :
    ∃ L : ℝ, ∀ r ∈ Ioo (0 : ℝ) R,
      ‖particular p.exponent (radialCorrection s) (tangentCorrection s) r‖ ≤ L*r := by
  obtain ⟨Cr,hCr⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    (radialCorrection_continuous s).continuousOn
  obtain ⟨Ct,hCt⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    (tangentCorrection_continuous s).continuousOn
  let Mp := max (max Cr Ct) 0
  have hMp : 0 ≤ Mp := le_max_right _ _
  refine ⟨ConicalParticularBounds.constant p.exponent*Mp,?_⟩
  intro r hr
  exact ConicalParticularBounds.particular_norm_le p.exponent ⟨p.exponent_pos,hν⟩ _ _
    (radialCorrection_continuous s).continuousOn (tangentCorrection_continuous s).continuousOn r Mp hr.1 hMp
    (fun t ht => ⟨(hCr t ⟨ht.1.le,ht.2.le.trans hr.2.le⟩).trans ((le_max_left _ _).trans (le_max_left _ _)),
      (hCt t ⟨ht.1.le,ht.2.le.trans hr.2.le⟩).trans ((le_max_right _ _).trans (le_max_left _ _))⟩)

theorem coefficient_scaled (p : Data) (b : ℝ) (hb : 0 < b) (hν : p.exponent < 1)
    (s s' : System p b) (z : ℂ)
    (htot : ∀ i : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate s' i x=z*totalCoordinate s i x)
    (q q' : ℂ)
    (he : projected p s.graph =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
      q*power p.exponent r+particular p.exponent (radialCorrection s) (tangentCorrection s) r)
    (he' : projected p s'.graph =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
      q'*power p.exponent r+particular p.exponent (radialCorrection s') (tangentCorrection s') r) :
    q'=z*q := by
  by_contra hne
  have hc : q'-z*q≠0 := sub_ne_zero.mpr hne
  obtain ⟨L1,h1⟩ := particular_bound p b hν s b
  obtain ⟨L2,h2⟩ := particular_bound p b hν s' b
  obtain ⟨C1,hC1⟩ := tangent_bound p b s b
  obtain ⟨C2,hC2⟩ := tangent_bound p b s' b
  have hν' : p.exponent ∈ Ioo (0 : ℝ) 1 := ⟨p.exponent_pos,hν⟩
  have hd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) b) :=
    particular_hasDerivAt _ hν' _ _ (radialCorrection_continuous s).continuousOn
      (tangentCorrection_continuous s).continuousOn r hr.1
  have hd' (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) b) :=
    particular_hasDerivAt _ hν' _ _ (radialCorrection_continuous s').continuousOn
      (tangentCorrection_continuous s').continuousOn r hr.1
  apply ConicalRadialUnbounded.nonzero_power_not_linear_bounded p.exponent b hν' hb (q'-z*q) hc
    (fun r => particular p.exponent (radialCorrection s') (tangentCorrection s') r-
      z*particular p.exponent (radialCorrection s) (tangentCorrection s) r)
    (fun r hr => (((hd' r hr).continuousAt).sub (continuousAt_const.mul (hd r hr).continuousAt)).continuousWithinAt)
    (L2+‖z‖*L1)
  · intro r hr
    apply (norm_sub_le _ _).trans
    rw [norm_mul]
    calc
      _ ≤ L2*r+‖z‖*(L1*r) := add_le_add (h2 r hr) (mul_le_mul_of_nonneg_left (h1 r hr) (norm_nonneg _))
      _ = _ := by ring
  · refine ⟨(C2+‖z‖*C1)/p.eigenvalue,?_⟩
    have hT := tangentTotal_scaled p b s s' z htot
    have hts := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self (a := (0 : ℝ)) (b := b))
      (ConicalLocalFlux.tangentTotal_ae s)
    have hts' := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self (a := (0 : ℝ)) (b := b))
      (ConicalLocalFlux.tangentTotal_ae s')
    filter_upwards [he,he',hT,hts,hts',ae_restrict_mem measurableSet_Ioo] with r e e' hTr t1 t2 hm
    have key : (q'-z*q)*power p.exponent r+(particular p.exponent (radialCorrection s') (tangentCorrection s') r-
        z*particular p.exponent (radialCorrection s) (tangentCorrection s) r)=
        (r : ℂ)/(p.eigenvalue : ℂ)*(z*tangentCorrection s r-tangentCorrection s' r) := by
      have ee : (q'-z*q)*power p.exponent r+(particular p.exponent (radialCorrection s') (tangentCorrection s') r-
          z*particular p.exponent (radialCorrection s) (tangentCorrection s) r)=
          projected p s'.graph r-z*projected p s.graph r := by
        rw [e,e']
        ring
      rw [ee]
      have m1 : ConicalGraphMoments.tangentMoment p s'.graph r=
          ConicalLocalFlux.tangentTotal s' r-tangentCorrection s' r := by rw [t2]; ring
      have m2 : ConicalGraphMoments.tangentMoment p s.graph r=
          ConicalLocalFlux.tangentTotal s r-tangentCorrection s r := by rw [t1]; ring
      simp only [projected]
      rw [m1,m2,hTr]
      ring
    have hr0 : 0 < r := hm.1
    have hrc : r ∈ Icc (0 : ℝ) b := ⟨hm.1.le,hm.2.le⟩
    show ‖(q'-z*q)*power p.exponent r+(particular p.exponent (radialCorrection s') (tangentCorrection s') r-
        z*particular p.exponent (radialCorrection s) (tangentCorrection s) r)‖ ≤ _
    rw [key,norm_mul,norm_div,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_pos hr0,abs_of_pos (eigenvalue_pos p)]
    have hb2 : ‖z*tangentCorrection s r-tangentCorrection s' r‖ ≤ C2+‖z‖*C1 := by
      apply (norm_sub_le _ _).trans
      rw [norm_mul]
      have hh := add_le_add (mul_le_mul_of_nonneg_left (hC1 r hrc) (norm_nonneg z)) (hC2 r hrc)
      linarith
    calc
      _ ≤ r/p.eigenvalue*(C2+‖z‖*C1) :=
        mul_le_mul_of_nonneg_left hb2 (div_nonneg hr0.le (eigenvalue_pos p).le)
      _ = _ := by ring

theorem positive_frequency_normalized_input_coefficient_transfer (p : Data) (a b R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hR : 0 < R) (hRb : R < b) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (hk : 0 < k), k < δ →
      ∃ c' : ModeIndex →₀ ℂ, c'≠0 ∧
        Tendsto (FiniteMixedScaledFlux.inwardPowerK k c') atTop (𝓝 1) ∧
        ∃ (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
          (J : Field) (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
          (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=
            ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k c') i x)
          (q : ℂ), q≠0 ∧
          ConicalGraphProjection.projected p
            (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c') J
              (fun i => (hJ i).continuous) heJ).graph
            =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] (fun r =>
              q*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
                (radialCorrection (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq
                  (FiniteAngularHerglotz.incident k c') J (fun i => (hJ i).continuous) heJ))
                (tangentCorrection (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq
                  (FiniteAngularHerglotz.incident k c') J (fun i => (hJ i).continuous) heJ)) r) ∧
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
  obtain ⟨δ₀,hδ₀,hfix⟩ := ConicalFixedInputTransfer.positive_frequency_fixed_input_rounded_transfer
    p a b R ha hai hba hR hRb hν
  have hcrpos := MaterialVolumeLimit.commonRadius_positive p.contrast a p.contrast_nonnegative
  refine ⟨min δ₀ (MaterialVolumeLimit.commonRadius p.contrast a),lt_min hδ₀ hcrpos,?_⟩
  intro k hk hkd
  obtain ⟨hfreq,c,J,hJ,heJ,q,hc,hq,he,-,-,-⟩ := hfix k hk (hkd.trans_le (min_le_left _ _))
  have hcr : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  have hb0 : 0 < b := hR.trans hRb
  let z : ℂ := (k : ℂ)*(((Real.sqrt (FiniteMixedScaledFlux.E c))⁻¹ : ℝ) : ℂ)
  have hz : FiniteMixedScaledFlux.normalizeK k c=z • c := by
    unfold FiniteMixedScaledFlux.normalizeK FiniteMixedScaledFlux.normalize
    rw [smul_smul]
  have hne := FiniteMixedScaledFlux.normalizeK_ne_zero k hk c hc
  have hz0 : z≠0 := by
    intro h0
    apply hne
    rw [hz,h0,zero_smul]
  have hne' : z • c≠0 := hz ▸ hne
  obtain ⟨J',hJ',-,heJ'⟩ := ConicalEntireGauge.exists_incident_extension p a b k hai hba
    (FiniteAngularHerglotz.incident k (z • c))
  let s := ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J
    (fun i => (hJ i).continuous) heJ
  let s' := ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k (z • c)) J'
    (fun i => (hJ' i).continuous) heJ'
  have hsub : ball (0 : Space) b ⊆ closedBall (0 : Space) a := (ball_subset_ball hba.le).trans ball_subset_closedBall
  have htot : ∀ i : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate s' i x=z*totalCoordinate s i x := by
    intro i
    have h3 := (ae_restrict_iff' measurableSet_closedBall).mp
      (ConicalNormalizedInputTransfer.electric_smul_ae p a k z c i)
    filter_upwards [ConicalEntireGauge.system_total_inner p a b k ha hai hba hk.ne' hfreq
      (FiniteAngularHerglotz.incident k (z • c)) J' (fun i => (hJ' i).continuous) heJ' i,
      ConicalEntireGauge.system_total_inner p a b k ha hai hba hk.ne' hfreq
        (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ i,h3] with x a1 a2 a3 hx
    rw [a1 hx,a2 hx,a3 (hsub hx)]
  obtain ⟨q',he'⟩ := ConicalLocalExpansion.actual_projected_expansion s' hb0 (hba.trans hai) hν
  have hqq : q'=z*q := coefficient_scaled p b hb0 hν s s' z htot q q' he he'
  have hq' : q'≠0 := by
    rw [hqq]
    exact mul_ne_zero hz0 hq
  have hu := ConicalFixedInputTransfer.fixed_input_electric_not_essentially_bounded p a b k ha hai hba hν hk.ne'
    hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ q hq he
  refine ⟨z • c,hne',?_,hfreq,J',hJ',heJ',q',hq',he',
    ConicalFixedInputTransfer.ballField_tendsto p a k ha hcr _,
    fun n => ConicalFixedInputTransfer.rounded_maxwell p a k ha hcr n _,
    fun n => ConicalNormalizedInputHCurl.exists_regional_fields p a k ha n hcr _,?_⟩
  · rw [← hz]
    exact FiniteMixedScaledFlux.normalizedK_limit k hk c hc
  · intro R' hR' hR'b
    obtain ⟨i,hi⟩ := ConicalVolumePeaks.coordinate_unbounded
      (ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k c)) _ (hu R' hR' hR'b)
    have hi' := ConicalNormalizedInputTransfer.unbounded_smul p a k R' (hR'b.trans hba.le) z hz0 c i hi
    exact ⟨i,fun M => ConicalFixedInputTransfer.eventually_high_superlevel p a k R' ha (hR'b.trans hba.le) hcr
      (FiniteAngularHerglotz.incident k (z • c)) i hi' M⟩

end OQ14.ConicalNormalizedInputCoefficient
#print axioms OQ14.ConicalNormalizedInputCoefficient.tangentTotal_scaled
#print axioms OQ14.ConicalNormalizedInputCoefficient.tangent_bound
#print axioms OQ14.ConicalNormalizedInputCoefficient.particular_bound
#print axioms OQ14.ConicalNormalizedInputCoefficient.coefficient_scaled
#print axioms OQ14.ConicalNormalizedInputCoefficient.positive_frequency_normalized_input_coefficient_transfer
