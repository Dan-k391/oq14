import CommonTotalPairStability
import ConicalCommonCorrectionUniform
import ConicalCommonDetection
import ConicalCommonGaugeIdentity
import CommonActualJointApprox
import ConicalCommonSingleInput

/-! Transfer the actual common-material witness coefficients to one finite angular input. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.ConicalCommonRungeNonzero
open MeasureTheory Set Metric Filter
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem functional_ne_zero (i : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hk : 0 < k) (hb0 : 0 < b) (hb : b < a i) (hν : (p i).exponent < 1)
    (hra : ∀ j, 0 ≤ a j) (hgeom : ∀ j l, j ≠ l → a j+a l < dist (center j) (center l))
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hKR : UnionFreeRunge.balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hai : ∀ j, a j < (p j).cutoff.rIn)
    (hq : ConicalIntrinsicCoefficient.coefficient
      (ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k b hR0 hk.ne' hb hfreq hR
        (fun j => (hR j).trans (closedBall_subset_closedBall hRT)) hai) hb0 (hb.trans (hai i)) hν ≠ 0) :
    ConicalCommonAngular.coefficientLinear p a center B hB hcontrast ha hsep i R k b hR0 hk.ne' hb.le (hai i) hfreq hR hb0 hν ≠ 0 := by
  let r : ℝ := b/2
  have hr0 : 0 < r := by dsimp [r]; linarith
  have hrb : r < b := by dsimp [r]; linarith
  let ζ : ℝ → ℝ := ConicalSeparatedRetention.annularBump r hr0
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := (ConicalSeparatedRetention.annularBump r hr0).contDiff
  have hc : HasCompactSupport ζ := (ConicalSeparatedRetention.annularBump r hr0).hasCompactSupport
  have hs : tsupport ζ ⊆ Ioo (0 : ℝ) r := ConicalSeparatedRetention.annularBump_support r hr0
  let hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T :=
    fun j => (hR j).trans (closedBall_subset_closedBall hRT)
  let t := ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k b hR0 hk.ne' hb hfreq hR hT hai
  let N := ConicalCoefficientStability.numerator t ζ hζ hc
  have hN : N ≠ 0 := ConicalCommonDetection.numerator_ne_zero_of_coefficient (p i) b r hb0 hr0 hrb
    (hb.trans (hai i)) hν t hq
  obtain ⟨P,Q,hP,hQ,hpair⟩ := CommonTotalPairStability.uniform_bound p a center B hB hcontrast ha hsep i R T k b
    hR0 hRT hk.ne' hb hfreq hKR hR hT hai ζ hζ hc (hs.trans (Ioo_subset_Ioo_right hrb.le))
  obtain ⟨C,D,hC,hD,hcorr⟩ := ConicalCommonCorrectionUniform.correction_difference_bound p a center B hB hcontrast ha hsep i R T k b
    hR0 hRT hk.ne' hb hfreq hR hai hKR
  obtain ⟨G,hG,hnum⟩ := ConicalCoefficientStability.numerator_difference_bound (p i) hν r ζ hζ hc hs
  let K : ℝ := P+Q+G*(C+D)+1
  have hK : 0 < K := by dsimp [K]; positivity
  let ε : ℝ := ‖N‖/(2*K)
  have hε : 0 < ε := div_pos (norm_pos_iff.mpr hN) (by positivity)
  obtain ⟨d, herr, hsol⟩ := CommonActualJointApprox.joint_actual p a center B hB hcontrast ha hsep i R T k hk
    hR0 hRT hra hgeom hKR hR hai ε hε
  obtain ⟨J,hJ,heJ⟩ := ConicalCommonFixedGauge.exists_extension p center i (a i) b k (hai i) hb d
  let s := ConicalCommonFixedGauge.system p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk.ne' hb hfreq hR hai d J
    (fun j => (hJ j).continuous) heJ
  have hsol' : ‖CommonTotalError.solutionDifference p a center B hB hcontrast ha hsep i R T k hKR d‖ < ε := by
    unfold CommonTotalError.solutionDifference
    rw [← CommonIncidentSolutionBridge.solution_eq p a center B hB hcontrast ha hsep R k hKR hR d]
    exact hsol
  have hp := hpair d J (fun j => (hJ j).continuous) heJ
  have hM : 0 ≤ C*‖ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR (hT i) d‖ +
      D*‖ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d)-
        ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ := by positivity
  have hw := hcorr d J (fun j => (hJ j).continuous) heJ
  have hw' : ∀ j x, x ∈ closedBall (0 : Space) r → ‖s.correction j x-t.correction j x‖ ≤
      C*‖ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR (hT i) d‖ +
      D*‖ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d)-
        ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k‖ :=
    fun j x hx => hw j x (closedBall_subset_closedBall hrb.le hx)
  have hn := hnum s t hrb.le _ hM hw'
  have hdist : ‖ConicalCoefficientStability.numerator s ζ hζ hc - N‖ < ‖N‖ := by
    change ‖ConicalCoefficientStability.numerator s ζ hζ hc - ConicalCoefficientStability.numerator t ζ hζ hc‖ ≤ _ at hn
    have hscale : 2*K*ε = ‖N‖ := by dsimp [ε]; field_simp
    have hPerr := mul_le_mul_of_nonneg_left herr.le hP
    have hQsol := mul_le_mul_of_nonneg_left hsol'.le hQ
    have hCerr := mul_le_mul_of_nonneg_left herr.le hC
    have hDsol := mul_le_mul_of_nonneg_left hsol.le hD
    dsimp only [N]
    dsimp [K] at hscale
    nlinarith
  have hnz : ConicalCoefficientStability.numerator s ζ hζ hc ≠ 0 := by
    intro hz
    rw [hz, zero_sub, norm_neg] at hdist
    exact (lt_irrefl _ hdist)
  have hqfixed := ConicalCommonDetection.coefficient_ne_zero_of_numerator (p i) b hb0 (hb.trans (hai i)) hν s ζ hζ hc
    (hs.trans (Ioo_subset_Ioo_right hrb.le)) hnz
  have hqangular := ConicalCommonGaugeIdentity.coefficient_eq_fixed p a center B hB hcontrast ha hsep i R T k b hR0 hRT
    hk.ne' hb hb0 hν hfreq hR hai d J (fun j => (hJ j).continuous) heJ
  intro hzero
  have heval := congrArg (fun F : Input →ₗ[ℂ] ℂ => F d) hzero
  change ConicalCommonAngular.coefficient p a center B hB hcontrast ha hsep i R k b hR0 hk.ne' hb.le (hai i) hfreq hR hb0 hν d = 0 at heval
  exact hqfixed (hqangular.symm.trans heval)

theorem one_normalized_illumination [Nonempty ι] (R T : ℝ) (b : ι → ℝ)
    (hR0 : 0 ≤ R) (hRT : R ≤ T) (hb0 : ∀ i, 0 < b i) (hb : ∀ i, b i < a i)
    (hν : ∀ i, (p i).exponent < 1) (hra : ∀ i, 0 ≤ a i)
    (hgeom : ∀ i j, i ≠ j → a i+a j < dist (center i) (center j))
    (hKR : UnionFreeRunge.balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hai : ∀ i, a i < (p i).cutoff.rIn) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, ∀ (hk : 0 < k), k < δ →
      ∃ (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
        (d : Input), d ≠ 0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK k d) atTop (𝓝 1) ∧
        (∀ i, ConicalCommonAngular.coefficient p a center B hB hcontrast ha hsep i R k (b i) hR0 hk.ne'
          (hb i).le (hai i) hfreq hR (hb0 i) (hν i) d ≠ 0) ∧
        MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep))
          (ConicalCommonEntire.electric p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d))
          (ConicalCommonEntire.magnetic p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d)) := by
  have hRT0 : 0 ≤ R+T := by linarith
  let hT : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T :=
    fun i => (hR i).trans (closedBall_subset_closedBall hRT)
  obtain ⟨δ,hδ,hbase⟩ := ConicalCommonNonzero.simultaneous_baseline_nonzero p a center B hB hcontrast ha hsep
    R T b hR0 hRT0 hb0 hb hν hR hT hai
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨hfreq,_⟩ := hbase k hk hkd i
  have hne : ∀ i, ConicalCommonSingleInput.functional p a b center B hB hcontrast ha hsep R k hR0 hk
      (fun i => (hb i).le) hai hfreq hR hb0 hν i ≠ 0 := by
    intro i
    obtain ⟨hf,hq⟩ := hbase k hk hkd i
    exact functional_ne_zero p a center B hB hcontrast ha hsep i R T k (b i) hR0 hRT hk (hb0 i) (hb i) (hν i)
      hra hgeom hfreq hKR hR hai hq
  obtain ⟨d,hd,hpower,hq,hm⟩ := ConicalCommonSingleInput.normalized_common_input p a b center B hB hcontrast ha hsep
    R k hR0 hk (fun i => (hb i).le) hai hfreq hR hb0 hν hne
  exact ⟨hfreq,d,hd,hpower,hq,hm⟩

end OQ14.ConicalCommonRungeNonzero
#print axioms OQ14.ConicalCommonRungeNonzero.functional_ne_zero
#print axioms OQ14.ConicalCommonRungeNonzero.one_normalized_illumination
