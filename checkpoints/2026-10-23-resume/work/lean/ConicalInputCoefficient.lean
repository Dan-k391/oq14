import ConicalGaugeStability

/-! Actual annular extraction error is bounded by incident ball L2 error. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.ConicalInputCoefficient
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
open scoped Topology
abbrev Space := Maxwell.Space

theorem restrict_extension_ae (a R : ℝ) (hRa : R ≤ a) (g : ConicalRungeBall.BallL2 a) (E : Field)
    (hg : ∀ i, (g i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => E x i) (i : Fin 3) :
    (ConicalBallRestriction.vector R (ConicalBallExtension.vector a g) i : Space → ℂ)
      =ᵐ[volume.restrict (closedBall (0 : Space) R)] fun x => E x i := by
  have hi := (ae_restrict_iff' measurableSet_closedBall).mp (hg i)
  filter_upwards [ConicalBallRestriction.vector_ae R (ConicalBallExtension.vector a g) i,
    ae_restrict_of_ae (ConicalBallExtension.vector_ae a g i),ae_restrict_of_ae hi,
    ae_restrict_mem measurableSet_closedBall] with x hr he hi hx
  rw [hr,he,indicator_of_mem (closedBall_subset_closedBall hRa hx),hi (closedBall_subset_closedBall hRa hx)]

def fieldOperator (p : Data) (a R k : ℝ) :
    ConicalRungeBall.BallL2 a →L[ℂ] ConicalRungeBall.BallL2 R :=
  (ConicalBallRestriction.vector R).comp ((ConicalBallExtension.vector a).comp
    (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a))

theorem finite_field_ae (p : Data) (a R k : ℝ) (hRa : R ≤ a)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3) :
    (fieldOperator p a R k (ConicalFinitePlanes.restricted k a c) i : Space → ℂ)
      =ᵐ[volume.restrict (closedBall (0 : Space) R)] fun x => ConicalFiniteGauge.electric p a k c x i :=
  restrict_extension_ae a R hRa _ _ (ConicalMaterialRunge.total_ae (ConicalSeparatedSource.material p a) k a _ _
    (ConicalSeparatedSource.material_compact p a) (ConicalFinitePlanes.restricted_ae k a c)) i

theorem baseline_field_ae (p : Data) (a R k : ℝ) (hai : a < p.cutoff.rIn) (hRa : R ≤ a) (i : Fin 3) :
    (fieldOperator p a R k (ConicalSeparatedIllumination.incidentBall p a k) i : Space → ℂ)
      =ᵐ[volume.restrict (closedBall (0 : Space) R)] fun x => ConicalSeparatedMaxwell.electric p a k x i := by
  have hg (j : Fin 3) : (ConicalMaterialRunge.totalOperator (ConicalSeparatedSource.material p a) k a
      (ConicalSeparatedIllumination.incidentBall p a k) j : Space → ℂ)
      =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => ConicalSeparatedMaxwell.electric p a k x j := by
    rw [ConicalSeparatedIllumination.incidentBall,ConicalSeparatedIllumination.total_restriction _ k a _
      (ConicalSeparatedSource.material_compact p a)]
    exact (ConicalBallRestriction.vector_ae a (ConicalSeparatedDynamic.field p a k) j).trans
      (ConicalSeparatedMaxwell.field_ae p a k hai j)
  exact restrict_extension_ae a R hRa _ _ hg i

theorem baseline_total_inner (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hba : b < a)
    (hk : k≠0) (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (i : Fin 3) : ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate (ConicalGaugeStability.baseline p a b k ha hai hba hk hfreq) i x=
        ConicalSeparatedMaxwell.electric p a k x i := by
  exact (ConicalSeparatedCorrection.totalCoordinate_inner p a k hai i).mono
    (fun x hx hm => hx (ball_subset_ball hba.le hm))

theorem numerator_error_bound (p : Data) (a b R k : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hRb : R < b) (hν : p.exponent < 1) (hk : k≠0)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field)
      (hJ : ∀ i, Continuous (fun x => J x i))
      (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x),
      ‖ConicalCoefficientStability.numerator
          (ConicalFiniteGauge.system p a b k ha hai hba hk hfreq c J hJ heJ) ζ hζ hc-
        ConicalCoefficientStability.numerator (ConicalGaugeStability.baseline p a b k ha hai hba hk hfreq) ζ hζ hc‖ ≤
      C*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖ := by
  obtain ⟨Cw,hCw,hw⟩ := ConicalGaugeStability.correction_difference_bound p a b k ha hai hba hk hfreq
  obtain ⟨Cn,hCn,hn⟩ := ConicalLocalPairing.numerator_difference_bound p hν R R ζ hζ hc hs le_rfl
  let A := fieldOperator p a R k
  let Cp := ‖ConicalLocalPairing.ballPair p R ζ hζ hc‖*‖A‖
  refine ⟨Cp+Cn*Cw,add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hCn hCw),?_⟩
  intro c J hJ heJ
  let s := ConicalFiniteGauge.system p a b k ha hai hba hk hfreq c J hJ heJ
  let t := ConicalGaugeStability.baseline p a b k ha hai hba hk hfreq
  let g := A (ConicalFinitePlanes.restricted k a c)
  let h := A (ConicalSeparatedIllumination.incidentBall p a k)
  have hg (i : Fin 3) : (g i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) R)] totalCoordinate s i := by
    filter_upwards [finite_field_ae p a R k ((hRb.trans hba).le) c i,
      ae_restrict_of_ae (ConicalFiniteGauge.system_total_inner p a b k ha hai hba hk hfreq c J hJ heJ i),
      ae_restrict_mem measurableSet_closedBall] with x hg hs hx
    exact hg.trans (hs (closedBall_subset_ball hRb hx)).symm
  have hh (i : Fin 3) : (h i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) R)] totalCoordinate t i := by
    filter_upwards [baseline_field_ae p a R k hai ((hRb.trans hba).le) i,
      ae_restrict_of_ae (baseline_total_inner p a b k ha hai hba hk hfreq i),
      ae_restrict_mem measurableSet_closedBall] with x hg hs hx
    exact hg.trans (hs (closedBall_subset_ball hRb hx)).symm
  have hb := hn s t hRb.le g h hg hh
    (Cw*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖)
    (mul_nonneg hCw (norm_nonneg _))
    (fun i x hx => hw c J hJ heJ i x (closedBall_subset_closedBall hRb.le hx))
  have hnorm : ‖g-h‖ ≤ ‖A‖*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖ := by
    change ‖A _-A _‖ ≤ _
    rw [← map_sub]
    exact A.le_opNorm _
  exact hb.trans ((add_le_add_right (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)) _).trans_eq (by dsimp only [Cp]; ring))

end OQ14.ConicalInputCoefficient
#print axioms OQ14.ConicalInputCoefficient.restrict_extension_ae
#print axioms OQ14.ConicalInputCoefficient.finite_field_ae
#print axioms OQ14.ConicalInputCoefficient.baseline_field_ae
#print axioms OQ14.ConicalInputCoefficient.baseline_total_inner
#print axioms OQ14.ConicalInputCoefficient.numerator_error_bound
