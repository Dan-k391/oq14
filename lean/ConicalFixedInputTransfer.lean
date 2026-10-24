import ConicalFixedAngularInput
import ConicalSeparatedRounding

/-! Transfer of one fixed finite transverse harmonic input through the literal rounded material family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ConicalFixedInputTransfer
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalProjectionData OQ14.ConicalRadialParticular OQ14.ConicalGraphProjection OQ14.PolarMomentTesting
  OQ14.ConicalRungeBall
open scoped Topology
abbrev Space := Maxwell.Space
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex

/-- The literal rounded-material total electric field for an arbitrary actual entire incident field. -/
def electric (p : Data) (a k : ℝ) (n : ℕ) (I : ConicalEntireGauge.Incident k) : Field :=
  MaterialField.total (ConicalSeparatedRounding.material p a n) k
    (ConicalMaterialRunge.solutionOperator (ConicalSeparatedRounding.material p a n) k a
      (ConicalEntireGauge.restricted a I)) I.E

def magnetic (p : Data) (a k : ℝ) (n : ℕ) (I : ConicalEntireGauge.Incident k) : Field :=
  MaterialMaxwell.totalMagnetic (ConicalSeparatedRounding.material p a n) k
    (ConicalMaterialRunge.solutionOperator (ConicalSeparatedRounding.material p a n) k a
      (ConicalEntireGauge.restricted a I)) I.H

theorem projected_bounded_of_system (p : Data) (b R : ℝ) (s : System p b) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ i : Fin 3, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖s.graph.gradient i x‖ ≤ B) :
    ∃ N : ℝ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R), ‖projected p s.graph r‖ ≤ N*r := by
  obtain ⟨C,hC,hb⟩ := ConicalTangentialDivergence.weightedTangent_bound p.eigenvalue p.contrast p.threshold
    p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one
  have hσ (i : Fin 3) (n : Sphere) : ‖ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i n‖ ≤ C := by
    rw [ConicalMomentWeights.tangent_sphere,Complex.norm_real]
    exact (PiLp.norm_apply_le _ i).trans (hb n)
  let D := B*C*(angularMeasure univ).toReal
  have hm (i : Fin 3) : ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) R),
      ‖moment (s.graph.gradient i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r‖ ≤ D :=
    PolarMomentBound.moment_bound_ae _ R B C hB _ (hσ i) (hg i)
  refine ⟨3*D/p.eigenvalue,?_⟩
  filter_upwards [ae_all_iff.mpr hm,ae_restrict_mem measurableSet_Ioo] with r hr hp
  have hsum : ‖ConicalGraphMoments.tangentMoment p s.graph r‖ ≤ 3*D := by
    calc
      _ ≤ ∑ i : Fin 3, ‖moment (s.graph.gradient i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, D := Finset.sum_le_sum (fun i _ => hr i)
      _ = _ := by simp only [Fin.sum_univ_three]; ring
  simp only [projected,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hp.1,abs_of_pos (ConicalGraphProjection.eigenvalue_pos p)]
  exact (mul_le_mul_of_nonneg_left hsum (div_nonneg hp.1.le (ConicalGraphProjection.eigenvalue_pos p).le)).trans_eq (by ring)

theorem not_essentially_bounded (p : Data) (b : ℝ) (hν : p.exponent < 1)
    (s : System p b) (E : Field)
    (hE : ∀ i : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b → totalCoordinate s i x = E x i)
    (q : ℂ) (hq : q≠0)
    (he : projected p s.graph =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
      q*power p.exponent r+particular p.exponent (radialCorrection s) (tangentCorrection s) r)
    (R : ℝ) (hR : 0 < R) (hRb : R ≤ b) :
    ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖E x‖ ≤ M := by
  rintro ⟨M0,hM0⟩
  have hM : 0 ≤ max M0 0 := le_max_right _ _
  have hE' : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖E x‖ ≤ max M0 0 :=
    hM0.mono (fun x hx => hx.trans (le_max_left _ _))
  have hW : Continuous (fun x : Space => fun i : Fin 3 => s.correction i x) := continuous_pi s.continuous
  obtain ⟨CW,hCW⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hW.continuousOn
  let B := max M0 0+max CW 0
  have hB : 0 ≤ B := add_nonneg hM (le_max_right _ _)
  have hg (i : Fin 3) : ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖s.graph.gradient i x‖ ≤ B := by
    filter_upwards [ae_restrict_of_ae (totalCoordinate_ae s i),ae_restrict_of_ae (hE i),hE',
      ae_restrict_mem measurableSet_ball] with x ht hEx he' hm
    have hxb : x ∈ ball (0 : Space) b := ball_subset_ball hRb hm
    have hgx : s.graph.gradient i x=E x i-s.correction i x := by
      rw [← hEx hxb,ht]; ring
    rw [hgx]
    apply (norm_sub_le _ _).trans
    exact add_le_add ((norm_le_pi_norm _ i).trans he')
      (((norm_le_pi_norm (fun j : Fin 3 => s.correction j x) i).trans
        (hCW x (ball_subset_closedBall hm))).trans (le_max_left _ _))
  obtain ⟨N,hN⟩ := projected_bounded_of_system p b R s B hB hg
  obtain ⟨Cr,hCr⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    (radialCorrection_continuous s).continuousOn
  obtain ⟨Ct,hCt⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := R)).exists_bound_of_continuousOn
    (tangentCorrection_continuous s).continuousOn
  let Mp := max (max Cr Ct) 0
  have hMp : 0 ≤ Mp := le_max_right _ _
  have hPb : ∀ r ∈ Ioo (0 : ℝ) R,
      ‖particular p.exponent (radialCorrection s) (tangentCorrection s) r‖ ≤
        (ConicalParticularBounds.constant p.exponent*Mp)*r := by
    intro r hr
    exact ConicalParticularBounds.particular_norm_le p.exponent ⟨p.exponent_pos,hν⟩ _ _
      (radialCorrection_continuous s).continuousOn (tangentCorrection_continuous s).continuousOn r Mp hr.1 hMp
      (fun t ht => ⟨(hCr t ⟨ht.1.le,ht.2.le.trans hr.2.le⟩).trans ((le_max_left _ _).trans (le_max_left _ _)),
        (hCt t ⟨ht.1.le,ht.2.le.trans hr.2.le⟩).trans ((le_max_right _ _).trans (le_max_left _ _))⟩)
  apply ConicalRadialUnbounded.nonzero_power_not_linear_bounded p.exponent R ⟨p.exponent_pos,hν⟩ hR q hq
    (particular p.exponent (radialCorrection s) (tangentCorrection s))
    (fun r hr => (particular_hasDerivAt _ ⟨p.exponent_pos,hν⟩ _ _
      (radialCorrection_continuous s).continuousOn (tangentCorrection_continuous s).continuousOn r hr.1).continuousAt.continuousWithinAt)
    (ConicalParticularBounds.constant p.exponent*Mp) hPb
  refine ⟨N,?_⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right hRb) he,hN] with r hr hm
  rwa [hr] at hm

theorem fixed_input_electric_not_essentially_bounded (p : Data) (a b k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hν : p.exponent < 1) (hk : k≠0)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (I : ConicalEntireGauge.Incident k) (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalEntireGauge.error p a k I i x)
    (q : ℂ) (hq : q≠0)
    (he : projected p (ConicalEntireGauge.system p a b k ha hai hba hk hfreq I J hJ heJ).graph
      =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
        q*power p.exponent r+particular p.exponent
          (radialCorrection (ConicalEntireGauge.system p a b k ha hai hba hk hfreq I J hJ heJ))
          (tangentCorrection (ConicalEntireGauge.system p a b k ha hai hba hk hfreq I J hJ heJ)) r)
    (R : ℝ) (hR : 0 < R) (hRb : R ≤ b) :
    ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
      ‖ConicalEntireGauge.electric p a k I x‖ ≤ M :=
  not_essentially_bounded p b hν _ (ConicalEntireGauge.electric p a k I)
    (fun i => ConicalEntireGauge.system_total_inner p a b k ha hai hba hk hfreq I J hJ heJ i) q hq he R hR hRb

theorem ballField_tendsto (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) (I : ConicalEntireGauge.Incident k) :
    Tendsto (fun n => ConicalMaterialRunge.totalOperator (ConicalSeparatedRounding.material p a n) k a
        (ConicalEntireGauge.restricted a I)) atTop
      (𝓝 (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
        (ConicalEntireGauge.restricted a I))) := by
  let g := ConicalEntireGauge.restricted a I
  let I' := ConicalBallExtension.vector a g
  have hleft : ConicalBallRestriction.vector a I'=g := ConicalBallRestriction.extension_leftInverse a g
  have hn (n : ℕ) : ConicalMaterialRunge.totalOperator (ConicalSeparatedRounding.material p a n) k a g=
      ConicalBallRestriction.vector a
        (MaterialVolumeLimit.volumeField (ConicalSeparatedRounding.material p a n) k a I') := by
    have h1 := ConicalSeparatedIllumination.total_restriction (ConicalSeparatedRounding.material p a n) k a I'
      (ConicalSeparatedRounding.common_support p a n)
    rwa [hleft] at h1
  have h0 : ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a g=
      ConicalBallRestriction.vector a
        (MaterialVolumeLimit.volumeField (ConicalSeparatedSource.material p a) k a I') := by
    have h1 := ConicalSeparatedIllumination.total_restriction (ConicalSeparatedSource.material p a) k a I'
      (ConicalSeparatedSource.material_compact p a)
    rwa [hleft] at h1
  have hfun : (fun n => ConicalMaterialRunge.totalOperator (ConicalSeparatedRounding.material p a n) k a g)=
      fun n => ConicalBallRestriction.vector a
        (MaterialVolumeLimit.volumeField (ConicalSeparatedRounding.material p a n) k a I') := funext hn
  change Tendsto (fun n => ConicalMaterialRunge.totalOperator (ConicalSeparatedRounding.material p a n) k a g) atTop
    (𝓝 (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a g))
  rw [hfun,h0]
  exact (ConicalBallRestriction.vector a).continuous.tendsto _ |>.comp
    (MaterialVolumeLimit.volumeField_tendsto (ConicalSeparatedRounding.material p a)
      (ConicalSeparatedSource.material p a) p.contrast k a ha (fun _ => le_rfl) le_rfl
      (ConicalSeparatedRounding.material_tendsto p a) hk I')

theorem rounded_maxwell (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) (n : ℕ) (I : ConicalEntireGauge.Incident k) :
    MaterialMaxwell.TestMaxwell k (ConicalSeparatedRounding.permittivity p a n) (electric p a k n I) (magnetic p a k n I) :=
  MaterialMaxwell.volume_solution_testMaxwell (ConicalSeparatedRounding.material p a n) k a
    (ConicalMaterialRunge.solutionOperator (ConicalSeparatedRounding.material p a n) k a (ConicalEntireGauge.restricted a I))
    (ConicalBallExtension.weighted (ConicalSeparatedRounding.material p a n) a (ConicalEntireGauge.restricted a I))
    I.E I.H (ConicalSeparatedRounding.common_support p a n)
    (ConicalMaterialRunge.weighted_actual _ a _ _ (ConicalSeparatedRounding.common_support p a n)
      (ConicalEntireGauge.restricted_ae a I))
    (ConicalMaterialRunge.solution_equation _ k a ha
      (hk.trans (MaterialVolumeLimit.commonRadius_le _ _ _ (by rw [ConicalSeparatedRounding.material_bound]))) _)
    (fun i => (I.smoothE i).continuous.locallyIntegrable)
    (fun i => (I.smoothH i).continuous.locallyIntegrable)
    (MaterialMaxwell.classical_vacuum_testMaxwell k I.E I.H
      (fun i => (I.smoothE i).of_le (by simp)) (fun i => (I.smoothH i).of_le (by simp)) I.maxwell)

theorem eventually_high_superlevel (p : Data) (a k R : ℝ) (ha : 0 ≤ a) (hRR : R ≤ a)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) (I : ConicalEntireGauge.Incident k)
    (i : Fin 3) (hi : ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
      ‖ConicalEntireGauge.electric p a k I x i‖ ≤ M) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < (volume.restrict (ball (0 : Space) R)) {x | M < ‖electric p a k n I x i‖} := by
  have hs : ball (0 : Space) R ⊆ closedBall (0 : Space) a :=
    (ball_subset_ball hRR).trans ball_subset_closedBall
  have hlim : ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
      (ConicalEntireGauge.restricted a I) ∉ ConicalSeparatedRounding.boundedCoordinate a R M i := by
    intro hb
    apply hi
    refine ⟨M,?_⟩
    filter_upwards [hb,ae_restrict_of_ae_restrict_of_subset hs
      (ConicalMaterialRunge.total_ae (ConicalSeparatedSource.material p a) k a _ I.E
        (ConicalSeparatedSource.material_compact p a) (ConicalEntireGauge.restricted_ae a I) i)] with x hx he
    have he' : (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
        (ConicalEntireGauge.restricted a I) i : Space → ℂ) x=ConicalEntireGauge.electric p a k I x i := he
    rw [he'] at hx
    exact hx
  filter_upwards [(ballField_tendsto p a k ha hk I).eventually
    ((ConicalSeparatedRounding.boundedCoordinate_isClosed a R M i hRR).isOpen_compl.mem_nhds hlim)] with n hn
  have hnb : ¬∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖electric p a k n I x i‖ ≤ M := by
    intro h
    apply hn
    filter_upwards [h,ae_restrict_of_ae_restrict_of_subset hs
      (ConicalMaterialRunge.total_ae (ConicalSeparatedRounding.material p a n) k a _ I.E
        (ConicalSeparatedRounding.common_support p a n) (ConicalEntireGauge.restricted_ae a I) i)] with x hx he
    have he' : (ConicalMaterialRunge.totalOperator (ConicalSeparatedRounding.material p a n) k a
        (ConicalEntireGauge.restricted a I) i : Space → ℂ) x=electric p a k n I x i := he
    rw [he']
    exact hx
  rw [ae_iff] at hnb
  exact pos_iff_ne_zero.mpr (by simpa only [not_le] using hnb)

theorem rounded_transfer_of_nonzero_coefficient (p : Data) (a b k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hν : p.exponent < 1) (hk : k≠0)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (hcr : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a)
    (c : ModeIndex →₀ ℂ) (J : Field) (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
    (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=
      ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k c) i x)
    (q : ℂ) (hq : q≠0)
    (he : ConicalGraphProjection.projected p
        (ConicalEntireGauge.system p a b k ha hai hba hk hfreq (FiniteAngularHerglotz.incident k c) J
          (fun i => (hJ i).continuous) heJ).graph
        =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
          q*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
            (radialCorrection (ConicalEntireGauge.system p a b k ha hai hba hk hfreq (FiniteAngularHerglotz.incident k c) J
              (fun i => (hJ i).continuous) heJ))
            (tangentCorrection (ConicalEntireGauge.system p a b k ha hai hba hk hfreq (FiniteAngularHerglotz.incident k c) J
              (fun i => (hJ i).continuous) heJ)) r) :
    Tendsto (fun n => ConicalMaterialRunge.totalOperator (ConicalSeparatedRounding.material p a n) k a
        (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c))) atTop
      (𝓝 (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
        (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c)))) ∧
    (∀ n : ℕ, MaterialMaxwell.TestMaxwell k (ConicalSeparatedRounding.permittivity p a n)
      (electric p a k n (FiniteAngularHerglotz.incident k c)) (magnetic p a k n (FiniteAngularHerglotz.incident k c))) ∧
    ∀ R : ℝ, 0 < R → R ≤ b → ∃ i : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
      0 < (volume.restrict (ball (0 : Space) R))
        {x | M < ‖electric p a k n (FiniteAngularHerglotz.incident k c) x i‖} := by
  refine ⟨ballField_tendsto p a k ha hcr _,fun n => rounded_maxwell p a k ha hcr n _,?_⟩
  intro R hR hRb
  have hu := fixed_input_electric_not_essentially_bounded p a b k ha hai hba hν hk hfreq
    (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ q hq he R hR hRb
  obtain ⟨i,hi⟩ := ConicalVolumePeaks.coordinate_unbounded
    (ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k c)) _ hu
  exact ⟨i,fun M => eventually_high_superlevel p a k R ha (hRb.trans hba.le) hcr
    (FiniteAngularHerglotz.incident k c) i hi M⟩

theorem positive_frequency_fixed_input_rounded_transfer (p : Data) (a b R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hR : 0 < R) (hRb : R < b) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (hk : 0 < k), k < δ →
      ∃ (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
        (c : ModeIndex →₀ ℂ) (J : Field)
        (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
        (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=
          ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k c) i x)
        (q : ℂ), c≠0 ∧ q≠0 ∧
        ConicalGraphProjection.projected p
          (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J
            (fun i => (hJ i).continuous) heJ).graph
          =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] (fun r =>
            q*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
              (radialCorrection (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J
                (fun i => (hJ i).continuous) heJ))
              (tangentCorrection (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J
                (fun i => (hJ i).continuous) heJ)) r) ∧
        Tendsto (fun n => ConicalMaterialRunge.totalOperator (ConicalSeparatedRounding.material p a n) k a
            (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c))) atTop
          (𝓝 (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
            (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c)))) ∧
        (∀ n : ℕ, MaterialMaxwell.TestMaxwell k (ConicalSeparatedRounding.permittivity p a n)
          (electric p a k n (FiniteAngularHerglotz.incident k c)) (magnetic p a k n (FiniteAngularHerglotz.incident k c))) ∧
        ∀ R' : ℝ, 0 < R' → R' ≤ b → ∃ i : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
          0 < (volume.restrict (ball (0 : Space) R'))
            {x | M < ‖electric p a k n (FiniteAngularHerglotz.incident k c) x i‖} := by
  obtain ⟨δ₀,hδ₀,hfix⟩ := ConicalFixedAngularInput.positive_frequency_fixed_input p a b R ha hai hba hR hRb hν
  have hcrpos := MaterialVolumeLimit.commonRadius_positive p.contrast a p.contrast_nonnegative
  refine ⟨min δ₀ (MaterialVolumeLimit.commonRadius p.contrast a),lt_min hδ₀ hcrpos,?_⟩
  intro k hk hkd
  obtain ⟨hfreq,c,J,hJ,heJ,q,hc,hq,he⟩ := hfix k hk (hkd.trans_le (min_le_left _ _))
  have hcr : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  exact ⟨hfreq,c,J,hJ,heJ,q,hc,hq,he,
    rounded_transfer_of_nonzero_coefficient p a b k ha hai hba hν hk.ne' hfreq hcr c J hJ heJ q hq he⟩

end OQ14.ConicalFixedInputTransfer
#print axioms OQ14.ConicalFixedInputTransfer.projected_bounded_of_system
#print axioms OQ14.ConicalFixedInputTransfer.not_essentially_bounded
#print axioms OQ14.ConicalFixedInputTransfer.fixed_input_electric_not_essentially_bounded
#print axioms OQ14.ConicalFixedInputTransfer.ballField_tendsto
#print axioms OQ14.ConicalFixedInputTransfer.rounded_maxwell
#print axioms OQ14.ConicalFixedInputTransfer.eventually_high_superlevel
#print axioms OQ14.ConicalFixedInputTransfer.rounded_transfer_of_nonzero_coefficient
#print axioms OQ14.ConicalFixedInputTransfer.positive_frequency_fixed_input_rounded_transfer
