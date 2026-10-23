import FiniteAngularNonzero
import ConicalEntireStability
import ConicalUniformBall
import ConicalFixedFiniteInput

/-! Choose one actual finite transverse harmonic input with a nonzero conical coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ConicalFixedAngularInput
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
open scoped Topology
abbrev Space := Maxwell.Space
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex

theorem exists_nonzero_numerator (p : Data) (a b R k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hRb : R < b) (hν : p.exponent < 1) (hk : 0 < k)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R)
    (hne : ConicalCoefficientStability.numerator
      (ConicalGaugeStability.baseline p a b k ha hai hba hk.ne' hfreq) ζ hζ hc≠0) :
    ∃ (d : ModeIndex →₀ ℂ) (J : Field)
      (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
      (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=
        ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k d) i x),
      d≠0 ∧ ConicalCoefficientStability.numerator
        (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k d)
          J (fun i => (hJ i).continuous) heJ) ζ hζ hc≠0 := by
  obtain ⟨C,hC,hbound⟩ := ConicalEntireStability.numerator_bound p a b R k ha hai hba hRb hν hk.ne' hfreq ζ hζ hc hs
  obtain ⟨Ci,hCi,hinc⟩ := ConicalIncidentEstimate.uniform_error_bound p a b k hai hba hk.ne'
  let N := ConicalCoefficientStability.numerator
    (ConicalGaugeStability.baseline p a b k ha hai hba hk.ne' hfreq) ζ hζ hc
  have hN : 0 < ‖N‖ := norm_pos_iff.mpr hne
  let K := ConicalUniformBall.factor a+Ci+2
  have hK : 0 < K := by dsimp only [K]; linarith [ConicalUniformBall.factor_nonnegative a]
  have hCp : 0 < C+1 := by linarith
  let δ := ‖N‖/(2*(C+1)*K)
  have hδ : 0 < δ := div_pos hN (by positivity)
  obtain ⟨c,hcapprox⟩ := ConicalSeparatedIllumination.finite_incident_approximation p a k ha hai hk δ hδ
  obtain ⟨d,hdne,hd⟩ := FiniteAngularNonzero.uniform_plane_approximation k a c δ hδ
  let I := FiniteAngularHerglotz.incident k d
  obtain ⟨J,hJ,hcomp,heJ⟩ := ConicalEntireGauge.exists_incident_extension p a b k hai hba I
  refine ⟨d,J,hJ,heJ,hdne,?_⟩
  have hdiff := ConicalUniformBall.restricted_difference a k I c δ hδ.le (fun x hx i => (hd x hx i).le)
  have hnorm : ‖ConicalEntireGauge.restricted a I-ConicalSeparatedIllumination.incidentBall p a k‖ ≤
      ConicalUniformBall.factor a*δ+δ := by
    have he : ConicalEntireGauge.restricted a I-ConicalSeparatedIllumination.incidentBall p a k=
        (ConicalEntireGauge.restricted a I-ConicalFinitePlanes.restricted k a c)+
          (ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k) := by abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add hdiff hcapprox.le)
  have herror : ∀ i x, x ∈ closedBall (0 : Space) b →
      ‖ConicalEntireGauge.error p a k I i x‖ ≤ δ+Ci*δ := by
    intro i x hx
    have ha' : x ∈ closedBall (0 : Space) a := closedBall_subset_closedBall hba.le hx
    have hi := hinc c i x hx
    have he : ConicalEntireGauge.error p a k I i x=
        (I.E x i-ConicalFinitePlanes.electric k c x i)+ConicalIncidentEstimate.error p a k c i x := by
      dsimp only [ConicalEntireGauge.error,ConicalIncidentEstimate.error]; ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (hd x ha' i).le
      (hi.trans (mul_le_mul_of_nonneg_left hcapprox.le hCi)))
  have hb := hbound I J (fun i => (hJ i).continuous) heJ (δ+Ci*δ) (by positivity) herror
  have hfinal : ‖ConicalCoefficientStability.numerator
      (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq I J (fun i => (hJ i).continuous) heJ) ζ hζ hc-N‖ < ‖N‖ := by
    apply hb.trans_lt
    calc
      _ ≤ C*(ConicalUniformBall.factor a*δ+δ+(δ+Ci*δ)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hnorm _) hC
      _ = C*K*δ := by dsimp only [K]; ring
      _ ≤ (C+1)*K*δ := by nlinarith
      _ = ‖N‖/2 := by dsimp only [δ]; field_simp; ring
      _ < ‖N‖ := by linarith
  intro hz
  rw [hz,zero_sub,norm_neg] at hfinal
  exact (lt_irrefl _) hfinal

theorem exists_nonzero_coefficient (p : Data) (a b R k : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hRb : R < b) (hν : p.exponent < 1) (hk : 0 < k)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R)
    (hne : ConicalCoefficientStability.numerator
      (ConicalGaugeStability.baseline p a b k ha hai hba hk.ne' hfreq) ζ hζ hc≠0) :
    ∃ (c : ModeIndex →₀ ℂ) (J : Field)
      (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
      (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k c) i x)
      (q : ℂ), c≠0 ∧ q≠0 ∧
      ConicalGraphProjection.projected p
        (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ).graph
        =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
          q*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
            (radialCorrection (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ))
            (tangentCorrection (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ)) r := by
  obtain ⟨c,J,hJ,heJ,hcne,hne⟩ := exists_nonzero_numerator p a b R k ha hai hba hRb hν hk hfreq ζ hζ hc hs hne
  let s := ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ
  obtain ⟨q,hq,he⟩ := ConicalLocalCoefficient.coefficient_identity s hb (hba.trans hai) hν ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right hRb.le))
  refine ⟨c,J,hJ,heJ,q,hcne,?_,hq⟩
  intro hz
  rw [hz,mul_zero,zero_mul,zero_add] at he
  exact hne (sub_eq_zero.mpr he)


theorem positive_frequency_fixed_input (p : Data) (a b R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hR : 0 < R) (hRb : R < b) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (hk : 0 < k), k < δ →
      ∃ (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
        (c : ModeIndex →₀ ℂ) (J : Field)
        (hJ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i))
        (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k c) i x)
        (q : ℂ), c≠0 ∧ q≠0 ∧
        ConicalGraphProjection.projected p
          (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ).graph
          =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
            q*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
              (radialCorrection (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ))
              (tangentCorrection (ConicalEntireGauge.system p a b k ha hai hba hk.ne' hfreq (FiniteAngularHerglotz.incident k c) J (fun i => (hJ i).continuous) heJ)) r := by
  have hN := ConicalFixedFiniteInput.eventually_nonzero_baseline p a R ha hai hR (hRb.trans hba).le hν
  have hfreq : ∀ᶠ k : ℝ in 𝓝 0, |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ)
      (DynamicStaticLimit.frequencyRadius_positive (ConicalSeparatedSource.material p a) a)] with k hk
    exact (show |k| < DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a from by
      simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs] using hk).le
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hN.and hfreq)
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  have hm : k ∈ ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos hk] using hkd
  obtain ⟨hN,hfreq⟩ := hsub hm
  refine ⟨hfreq,?_⟩
  apply exists_nonzero_coefficient p a b R k ha (hR.trans hRb) hai hba hRb hν hk hfreq
    (ConicalSeparatedRetention.annularBump R hR)
    (ConicalSeparatedRetention.annularBump R hR).contDiff
    (ConicalSeparatedRetention.annularBump R hR).hasCompactSupport
    (ConicalSeparatedRetention.annularBump_support R hR)
  rw [ConicalGaugeStability.baseline_numerator]
  exact hN


end OQ14.ConicalFixedAngularInput
#print axioms OQ14.ConicalFixedAngularInput.exists_nonzero_numerator
#print axioms OQ14.ConicalFixedAngularInput.exists_nonzero_coefficient
#print axioms OQ14.ConicalFixedAngularInput.positive_frequency_fixed_input
