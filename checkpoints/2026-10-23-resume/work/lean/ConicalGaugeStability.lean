import ConicalFiniteGauge
import ConicalLocalPairing
import ConicalSeparatedCorrection
import ConicalSeparatedRetention

/-! Actual finite-incident coefficient extraction in the identical separated-source gauge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalGaugeStability
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

def polarizationOperator (p : Data) (a k : ℝ) : ConicalRungeBall.BallL2 a →L[ℂ] VectorL2 :=
  (StaticCoefficient.sqrtMultiplier (ConicalSeparatedSource.material p a)).comp
    (ConicalMaterialRunge.solutionOperator (ConicalSeparatedSource.material p a) k a)

theorem baseline_solution (p : Data) (a k : ℝ) :
    ConicalMaterialRunge.solutionOperator (ConicalSeparatedSource.material p a) k a
      (ConicalSeparatedIllumination.incidentBall p a k)=ConicalSeparatedDynamic.solution p a k := by
  exact ConicalSeparatedIllumination.solution_restriction (ConicalSeparatedSource.material p a) k a
    (ConicalSeparatedDynamic.incident p a k) (ConicalSeparatedSource.material_compact p a)

theorem totalSource_difference (p : Data) (a k : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ) :
    ConicalFiniteGauge.totalSource p a k c-ConicalSeparatedMaxwell.totalSource p a k=
      polarizationOperator p a k (ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k) := by
  simp only [polarizationOperator,ContinuousLinearMap.comp_apply,map_sub,baseline_solution,
    ConicalFiniteGauge.totalSource,ConicalFiniteGauge.solution,ConicalSeparatedMaxwell.totalSource]
  abel

def baseline (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hba : b < a)
    (hk : k≠0) (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a) : System p b :=
  ConicalProjectionLocalization.ofPotential p b (hba.trans hai)
    (ConicalGradientGraph.separatedPotential p a k hai) (ConicalSeparatedPotential.correction p a k)
    (ConicalSeparatedPotential.correction_continuous p a k hai)
    (by
      intro f hf
      have he (i : Fin 3) : (∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
          ((ConicalGradientGraph.separatedPotential p a k hai).derivative i x+
            ConicalSeparatedPotential.correction p a k x i)*dcoord f x i)=
          ∫ x : Space, (ConicalSeparatedGauss.epsilon p x : ℂ)*ConicalSeparatedMaxwell.electric p a k x i*dcoord f x i := by
        apply integral_congr_ae
        filter_upwards with x
        dsimp only [ConicalGradientGraph.separatedPotential,ConicalLocalGauss.epsilon,ConicalSeparatedGauss.epsilon]
        ring
      simpa only [he] using ConicalSeparatedGauss.gauss_schwartz p a k ha hai hk hfreq f
        (hf.trans (ball_subset_ball hba.le)))

theorem baseline_numerator (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hba : b < a)
    (hk : k≠0) (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    ConicalCoefficientStability.numerator (baseline p a b k ha hai hba hk hfreq) ζ hζ hc=
      ConicalSeparatedPairing.gradientPair p a k hai ζ hζ hc-ConicalSeparatedIdentity.particularPair p a k ζ := rfl

theorem correction_difference_bound (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hba : b < a) (hk : k≠0)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field)
      (hJ : ∀ i, Continuous (fun x => J x i))
      (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x)
      (i : Fin 3) (x : Space), x ∈ closedBall (0 : Space) b →
      ‖(ConicalFiniteGauge.system p a b k ha hai hba hk hfreq c J hJ heJ).correction i x-
        (baseline p a b k ha hai hba hk hfreq).correction i x‖ ≤
          C*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖ := by
  obtain ⟨Ci,hCi,hinc⟩ := ConicalIncidentEstimate.uniform_error_bound p a b k hai hba hk
  let B : ℝ := k^2*‖polarizationOperator p a k‖*‖ScalarPotentialBound.cutoff 0 (b+p.cutoff.rOut)‖
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  refine ⟨Ci+B,add_nonneg hCi hB,?_⟩
  intro c J hJ heJ i x hx
  have hw := ConicalResponseLinear.correction_difference_bound k b p.cutoff.rOut
    (ConicalFiniteGauge.totalSource p a k c) (ConicalSeparatedMaxwell.totalSource p a k)
    (ConicalFiniteGauge.source p a k c) (ConicalSeparatedMaxwell.source p a k)
    (ConicalFiniteGauge.source_ae p a k c) (ConicalSeparatedMaxwell.source_ae p a k)
    (ConicalFiniteGauge.source_zero_outer p a k hai c) (ConicalSeparatedMaxwell.source_zero_outer p a k hai) i x hx
  have hp : ‖NewtonL2.physicalCoordinate (ConicalFiniteGauge.totalSource p a k c-
      ConicalSeparatedMaxwell.totalSource p a k) i‖ ≤
      ‖polarizationOperator p a k‖*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖ := by
    exact (DynamicConvolution.component_norm i _).trans (by
      rw [totalSource_difference]
      exact (polarizationOperator p a k).le_opNorm _)
  have hw' : ‖ElectricPotentialDecomposition.correction k (ConicalFiniteGauge.source p a k c) x i-
      ConicalSeparatedPotential.correction p a k x i‖ ≤
      B*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖ := by
    exact hw.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hp (sq_nonneg k)) (norm_nonneg _)).trans_eq (by dsimp only [B]; ring))
  have hin := hinc c i x hx
  change ‖ConicalGradientGraph.bump p.cutoff x*
    (J x i+ElectricPotentialDecomposition.correction k (ConicalFiniteGauge.source p a k c) x i)-
      ConicalGradientGraph.bump p.cutoff x*ConicalSeparatedPotential.correction p a k x i‖ ≤ _
  have he : ConicalGradientGraph.bump p.cutoff x=1 :=
    (ConicalGradientGraph.bump_inner p.cutoff x (closedBall_subset_ball (hba.trans hai) hx)).1
  rw [he,one_mul,one_mul]
  rw [heJ i x hx]
  have hs : ConicalIncidentEstimate.error p a k c i x+
      ElectricPotentialDecomposition.correction k (ConicalFiniteGauge.source p a k c) x i-
        ConicalSeparatedPotential.correction p a k x i=
      ConicalIncidentEstimate.error p a k c i x+
        (ElectricPotentialDecomposition.correction k (ConicalFiniteGauge.source p a k c) x i-
          ConicalSeparatedPotential.correction p a k x i) := by ring
  rw [hs]
  exact (norm_add_le _ _).trans ((add_le_add hin hw').trans_eq (by ring))

end OQ14.ConicalGaugeStability
#print axioms OQ14.ConicalGaugeStability.baseline_solution
#print axioms OQ14.ConicalGaugeStability.totalSource_difference
#print axioms OQ14.ConicalGaugeStability.baseline
#print axioms OQ14.ConicalGaugeStability.baseline_numerator
#print axioms OQ14.ConicalGaugeStability.correction_difference_bound
