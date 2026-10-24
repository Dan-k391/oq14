import ConicalFixedInputTransfer
import FiniteMixedScaledFlux

/-! Transfer of the unit-limit inward-flux normalized fixed finite input through the rounded family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ConicalNormalizedInputTransfer
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalRungeBall
open scoped Topology
abbrev Space := Maxwell.Space
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex

theorem amplitude_smul_apply (z : ℂ) (c : ModeIndex →₀ ℂ) (n : SphereReactionKernel.Sphere) (i : Fin 3) :
    FiniteVectorAngular.amplitude (z • c) n i=z*FiniteVectorAngular.amplitude c n i := by
  have h := congrArg (fun f => f n i) (FiniteMixedScaledFlux.amplitude_smul z c)
  exact h

theorem incident_E_smul (k : ℝ) (z : ℂ) (c : ModeIndex →₀ ℂ) (x : Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident k (z • c)).E x i=z*(FiniteAngularHerglotz.incident k c).E x i := by
  change SphereWaveCalculus.moment (fun θ => FiniteVectorAngular.amplitude (z • c) θ i) (-k) x=
    z*SphereWaveCalculus.moment (fun θ => FiniteVectorAngular.amplitude c θ i) (-k) x
  unfold SphereWaveCalculus.moment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with θ
  rw [amplitude_smul_apply]
  ring

theorem restricted_smul (a k : ℝ) (z : ℂ) (c : ModeIndex →₀ ℂ) :
    ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k (z • c))=
      z • ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c) := by
  apply PiLp.ext
  intro i
  rw [PiLp.smul_apply]
  apply Lp.ext
  filter_upwards [ConicalEntireGauge.restricted_ae a (FiniteAngularHerglotz.incident k (z • c)) i,
    Lp.coeFn_smul z (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c) i),
    ConicalEntireGauge.restricted_ae a (FiniteAngularHerglotz.incident k c) i] with x h1 h2 h3
  rw [h1,h2,Pi.smul_apply,h3,incident_E_smul,smul_eq_mul]

theorem electric_smul_ae (p : Data) (a k : ℝ) (z : ℂ) (c : ModeIndex →₀ ℂ) (i : Fin 3) :
    ∀ᵐ x : Space ∂volume.restrict (closedBall (0 : Space) a),
      ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k (z • c)) x i=
        z*ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k c) x i := by
  have h1 := ConicalMaterialRunge.total_ae (ConicalSeparatedSource.material p a) k a
    (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k (z • c)))
    (FiniteAngularHerglotz.incident k (z • c)).E (ConicalSeparatedSource.material_compact p a)
    (ConicalEntireGauge.restricted_ae a (FiniteAngularHerglotz.incident k (z • c))) i
  have h2 := ConicalMaterialRunge.total_ae (ConicalSeparatedSource.material p a) k a
    (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c))
    (FiniteAngularHerglotz.incident k c).E (ConicalSeparatedSource.material_compact p a)
    (ConicalEntireGauge.restricted_ae a (FiniteAngularHerglotz.incident k c)) i
  have key : ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
      (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k (z • c)))=
      z • ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
        (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c)) := by
    rw [restricted_smul,map_smul]
  have h3 : (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
      (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k (z • c))) i : Space → ℂ)
      =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => z*
        (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
          (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c)) i : Space → ℂ) x := by
    rw [key,PiLp.smul_apply]
    filter_upwards [Lp.coeFn_smul z (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
      (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c)) i)] with x hx
    rw [hx,Pi.smul_apply,smul_eq_mul]
  filter_upwards [h1,h2,h3] with x e1 e2 e3
  have e1' : (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
      (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k (z • c))) i : Space → ℂ) x=
      ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k (z • c)) x i := e1
  have e2' : (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
      (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c)) i : Space → ℂ) x=
      ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k c) x i := e2
  rw [← e1',e3,e2']

theorem unbounded_smul (p : Data) (a k R : ℝ) (hRR : R ≤ a) (z : ℂ) (hz : z≠0) (c : ModeIndex →₀ ℂ) (i : Fin 3)
    (hi : ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
      ‖ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k c) x i‖ ≤ M) :
    ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
      ‖ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k (z • c)) x i‖ ≤ M := by
  rintro ⟨M,hM⟩
  apply hi
  have hs : ball (0 : Space) R ⊆ closedBall (0 : Space) a :=
    (ball_subset_ball hRR).trans ball_subset_closedBall
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  refine ⟨M/‖z‖,?_⟩
  filter_upwards [hM,ae_restrict_of_ae_restrict_of_subset hs (electric_smul_ae p a k z c i)] with x hx he
  rw [he,norm_mul] at hx
  rw [le_div_iff₀ hzpos,mul_comm]
  exact hx

theorem positive_frequency_normalized_input_rounded_transfer (p : Data) (a b R : ℝ) (ha : 0 ≤ a)
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
  have hz : FiniteMixedScaledFlux.normalizeK k c=
      ((k : ℂ)*(((Real.sqrt (FiniteMixedScaledFlux.E c))⁻¹ : ℝ) : ℂ)) • c := by
    unfold FiniteMixedScaledFlux.normalizeK FiniteMixedScaledFlux.normalize
    rw [smul_smul]
  have hne := FiniteMixedScaledFlux.normalizeK_ne_zero k hk c hc
  have hz0 : ((k : ℂ)*(((Real.sqrt (FiniteMixedScaledFlux.E c))⁻¹ : ℝ) : ℂ))≠0 := by
    intro h0
    apply hne
    rw [hz,h0,zero_smul]
  refine ⟨FiniteMixedScaledFlux.normalizeK k c,hne,FiniteMixedScaledFlux.normalizedK_limit k hk c hc,
    ConicalFixedInputTransfer.ballField_tendsto p a k ha hcr _,
    fun n => ConicalFixedInputTransfer.rounded_maxwell p a k ha hcr n _,?_⟩
  intro R' hR' hR'b
  have hu := ConicalFixedInputTransfer.fixed_input_electric_not_essentially_bounded p a b k ha hai hba hν hk.ne'
    hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ q hq he R' hR' hR'b
  obtain ⟨i,hi⟩ := ConicalVolumePeaks.coordinate_unbounded
    (ConicalEntireGauge.electric p a k (FiniteAngularHerglotz.incident k c)) _ hu
  have hi' := unbounded_smul p a k R' (hR'b.trans hba.le) _ hz0 c i hi
  rw [← hz] at hi'
  exact ⟨i,fun M => ConicalFixedInputTransfer.eventually_high_superlevel p a k R' ha (hR'b.trans hba.le) hcr
    (FiniteAngularHerglotz.incident k (FiniteMixedScaledFlux.normalizeK k c)) i hi' M⟩

end OQ14.ConicalNormalizedInputTransfer
#print axioms OQ14.ConicalNormalizedInputTransfer.amplitude_smul_apply
#print axioms OQ14.ConicalNormalizedInputTransfer.incident_E_smul
#print axioms OQ14.ConicalNormalizedInputTransfer.restricted_smul
#print axioms OQ14.ConicalNormalizedInputTransfer.electric_smul_ae
#print axioms OQ14.ConicalNormalizedInputTransfer.unbounded_smul
#print axioms OQ14.ConicalNormalizedInputTransfer.positive_frequency_normalized_input_rounded_transfer
