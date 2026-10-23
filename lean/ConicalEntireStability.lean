import ConicalEntireGauge
import ConicalInputCoefficient

/-! Actual extraction is continuous in the incident ball norm and the fixed-gauge uniform error. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.ConicalEntireStability
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Incident := ConicalEntireGauge.Incident

theorem totalSource_difference (p : Data) (a k : ℝ) (I : Incident k) :
    ConicalEntireGauge.totalSource p a k I-ConicalSeparatedMaxwell.totalSource p a k=
      ConicalGaugeStability.polarizationOperator p a k
        (ConicalEntireGauge.restricted a I-ConicalSeparatedIllumination.incidentBall p a k) := by
  simp only [ConicalGaugeStability.polarizationOperator,ContinuousLinearMap.comp_apply,map_sub,
    ConicalGaugeStability.baseline_solution,ConicalEntireGauge.totalSource,ConicalEntireGauge.solution,
    ConicalSeparatedMaxwell.totalSource]
  abel

theorem field_ae (p : Data) (a R k : ℝ) (hRa : R ≤ a) (I : Incident k) (i : Fin 3) :
    (ConicalInputCoefficient.fieldOperator p a R k (ConicalEntireGauge.restricted a I) i : Space → ℂ)
      =ᵐ[volume.restrict (closedBall (0 : Space) R)] fun x => ConicalEntireGauge.electric p a k I x i :=
  ConicalInputCoefficient.restrict_extension_ae a R hRa _ _
    (ConicalMaterialRunge.total_ae (ConicalSeparatedSource.material p a) k a _ _
      (ConicalSeparatedSource.material_compact p a) (ConicalEntireGauge.restricted_ae a I)) i

theorem correction_bound (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hba : b < a) (hk : k≠0)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (I : Incident k) (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalEntireGauge.error p a k I i x)
    (e : ℝ) (he : ∀ i x, x ∈ closedBall (0 : Space) b → ‖ConicalEntireGauge.error p a k I i x‖ ≤ e)
    (i : Fin 3) (x : Space) (hx : x ∈ closedBall (0 : Space) b) :
    ‖(ConicalEntireGauge.system p a b k ha hai hba hk hfreq I J hJ heJ).correction i x-
      (ConicalGaugeStability.baseline p a b k ha hai hba hk hfreq).correction i x‖ ≤
      e+(k^2*‖ConicalGaugeStability.polarizationOperator p a k‖*‖ScalarPotentialBound.cutoff 0 (b+p.cutoff.rOut)‖)*
        ‖ConicalEntireGauge.restricted a I-ConicalSeparatedIllumination.incidentBall p a k‖ := by
  have hw := ConicalResponseLinear.correction_difference_bound k b p.cutoff.rOut
    (ConicalEntireGauge.totalSource p a k I) (ConicalSeparatedMaxwell.totalSource p a k)
    (ConicalEntireGauge.source p a k I) (ConicalSeparatedMaxwell.source p a k)
    (ConicalEntireGauge.source_ae p a k I) (ConicalSeparatedMaxwell.source_ae p a k)
    (ConicalEntireGauge.source_zero_outer p a k hai I) (ConicalSeparatedMaxwell.source_zero_outer p a k hai) i x hx
  have hp : ‖NewtonL2.physicalCoordinate (ConicalEntireGauge.totalSource p a k I-
      ConicalSeparatedMaxwell.totalSource p a k) i‖ ≤
      ‖ConicalGaugeStability.polarizationOperator p a k‖*
        ‖ConicalEntireGauge.restricted a I-ConicalSeparatedIllumination.incidentBall p a k‖ := by
    exact (DynamicConvolution.component_norm i _).trans (by
      rw [totalSource_difference]
      exact (ConicalGaugeStability.polarizationOperator p a k).le_opNorm _)
  have hw' := hw.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (sq_nonneg k)) (norm_nonneg _))
  change ‖ConicalGradientGraph.bump p.cutoff x*
    (J x i+ElectricPotentialDecomposition.correction k (ConicalEntireGauge.source p a k I) x i)-
      ConicalGradientGraph.bump p.cutoff x*ConicalSeparatedPotential.correction p a k x i‖ ≤ _
  rw [(ConicalGradientGraph.bump_inner p.cutoff x (closedBall_subset_ball (hba.trans hai) hx)).1,
    one_mul,one_mul,heJ i x hx]
  have hs : ConicalEntireGauge.error p a k I i x+
      ElectricPotentialDecomposition.correction k (ConicalEntireGauge.source p a k I) x i-
        ConicalSeparatedPotential.correction p a k x i=
      ConicalEntireGauge.error p a k I i x+
        (ElectricPotentialDecomposition.correction k (ConicalEntireGauge.source p a k I) x i-
          ConicalSeparatedPotential.correction p a k x i) := by ring
  rw [hs]
  exact (norm_add_le _ _).trans ((add_le_add (he i x hx) hw').trans_eq (by ring))

theorem numerator_bound (p : Data) (a b R k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hRb : R < b) (hν : p.exponent < 1) (hk : k≠0)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (I : Incident k) (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
      (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalEntireGauge.error p a k I i x)
      (e : ℝ), 0 ≤ e →
      (∀ i x, x ∈ closedBall (0 : Space) b → ‖ConicalEntireGauge.error p a k I i x‖ ≤ e) →
      ‖ConicalCoefficientStability.numerator
          (ConicalEntireGauge.system p a b k ha hai hba hk hfreq I J hJ heJ) ζ hζ hc-
        ConicalCoefficientStability.numerator (ConicalGaugeStability.baseline p a b k ha hai hba hk hfreq) ζ hζ hc‖ ≤
      C*(‖ConicalEntireGauge.restricted a I-ConicalSeparatedIllumination.incidentBall p a k‖+e) := by
  obtain ⟨Cn,hCn,hn⟩ := ConicalLocalPairing.numerator_difference_bound p hν R R ζ hζ hc hs le_rfl
  let A := ConicalInputCoefficient.fieldOperator p a R k
  let Cp := ‖ConicalLocalPairing.ballPair p R ζ hζ hc‖*‖A‖
  let B := k^2*‖ConicalGaugeStability.polarizationOperator p a k‖*‖ScalarPotentialBound.cutoff 0 (b+p.cutoff.rOut)‖
  have hCp : 0 ≤ Cp := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  refine ⟨Cp+Cn*(1+B),add_nonneg hCp (mul_nonneg hCn (by positivity)),?_⟩
  intro I J hJ heJ e he herror
  let s := ConicalEntireGauge.system p a b k ha hai hba hk hfreq I J hJ heJ
  let t := ConicalGaugeStability.baseline p a b k ha hai hba hk hfreq
  let g := A (ConicalEntireGauge.restricted a I)
  let h := A (ConicalSeparatedIllumination.incidentBall p a k)
  have hg (i : Fin 3) : (g i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) R)] totalCoordinate s i := by
    filter_upwards [field_ae p a R k ((hRb.trans hba).le) I i,
      ae_restrict_of_ae (ConicalEntireGauge.system_total_inner p a b k ha hai hba hk hfreq I J hJ heJ i),
      ae_restrict_mem measurableSet_closedBall] with x hg hs hx
    exact hg.trans (hs (closedBall_subset_ball hRb hx)).symm
  have hh (i : Fin 3) : (h i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) R)] totalCoordinate t i := by
    filter_upwards [ConicalInputCoefficient.baseline_field_ae p a R k hai ((hRb.trans hba).le) i,
      ae_restrict_of_ae (ConicalInputCoefficient.baseline_total_inner p a b k ha hai hba hk hfreq i),
      ae_restrict_mem measurableSet_closedBall] with x hg hs hx
    exact hg.trans (hs (closedBall_subset_ball hRb hx)).symm
  let d := ‖ConicalEntireGauge.restricted a I-ConicalSeparatedIllumination.incidentBall p a k‖
  have hd : 0 ≤ d := norm_nonneg _
  have hb := hn s t hRb.le g h hg hh (e+B*d) (add_nonneg he (mul_nonneg hB hd))
    (fun i x hx => correction_bound p a b k ha hai hba hk hfreq I J hJ heJ e herror i x
      (closedBall_subset_closedBall hRb.le hx))
  have hnorm : ‖g-h‖ ≤ ‖A‖*d := by
    change ‖A _-A _‖ ≤ _
    rw [←map_sub]
    exact A.le_opNorm _
  have hb' := hb.trans (add_le_add_right (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)) _)
  change _ ≤ (Cp+Cn*(1+B))*(d+e)
  have hb'' : _ ≤ Cp*d+Cn*(e+B*d) := hb'.trans_eq (by dsimp only [Cp]; ring)
  clear hb'
  nlinarith [mul_nonneg hCp he,mul_nonneg hCn hd,mul_nonneg (mul_nonneg hCn hB) he]

end OQ14.ConicalEntireStability
#print axioms OQ14.ConicalEntireStability.totalSource_difference
#print axioms OQ14.ConicalEntireStability.field_ae
#print axioms OQ14.ConicalEntireStability.correction_bound
#print axioms OQ14.ConicalEntireStability.numerator_bound
