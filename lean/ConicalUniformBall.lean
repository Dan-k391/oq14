import ConicalEntireGauge

/-! Uniform electric errors control the literal material-ball L2 restrictions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalUniformBall
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalRungeBall
open scoped ENNReal
abbrev Space := Maxwell.Space

def factor (a : ℝ) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarBall a)).symm.toContinuousLinearMap‖*
    (measureUnivNNReal (volume.restrict (closedBall (0 : Space) a)) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹

theorem factor_nonnegative (a : ℝ) : 0 ≤ factor a :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (NNReal.coe_nonneg _) _)

theorem norm_bound (a : ℝ) (g : BallL2 a) (e : ℝ) (he : 0 ≤ e)
    (hg : ∀ i, ∀ᵐ x : Space ∂volume.restrict (closedBall (0 : Space) a), ‖g i x‖ ≤ e) :
    ‖g‖ ≤ factor a*e := by
  let A := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarBall a)).symm.toContinuousLinearMap
  let M : ℝ := (measureUnivNNReal (volume.restrict (closedBall (0 : Space) a)) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  have hM : 0 ≤ M := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hpi : ‖fun i => g i‖ ≤ M*e := (pi_norm_le_iff_of_nonneg (mul_nonneg hM he)).mpr
    (fun i => Lp.norm_le_of_ae_bound he (hg i))
  have h := (A.le_opNorm (fun i => g i)).trans (mul_le_mul_of_nonneg_left hpi (norm_nonneg A))
  change ‖g‖ ≤ _ at h
  exact h.trans_eq (by dsimp only [factor,A,M]; ring)

theorem restricted_difference (a k : ℝ) (I : ConicalEntireGauge.Incident k)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (e : ℝ) (he : 0 ≤ e)
    (herror : ∀ x ∈ closedBall (0 : Space) a, ∀ i : Fin 3,
      ‖I.E x i-ConicalFinitePlanes.electric k c x i‖ ≤ e) :
    ‖ConicalEntireGauge.restricted a I-ConicalFinitePlanes.restricted k a c‖ ≤ factor a*e := by
  apply norm_bound a _ e he
  intro i
  filter_upwards [Lp.coeFn_sub (ConicalEntireGauge.restricted a I i) (ConicalFinitePlanes.restricted k a c i),
    ConicalEntireGauge.restricted_ae a I i,ConicalFinitePlanes.restricted_ae k a c i,
    ae_restrict_mem measurableSet_closedBall] with x hs hI hc hx
  change ‖(ConicalEntireGauge.restricted a I i-ConicalFinitePlanes.restricted k a c i) x‖ ≤ e
  rw [hs]
  simpa only [Pi.sub_apply,hI,hc] using herror x hx i

end OQ14.ConicalUniformBall
#print axioms OQ14.ConicalUniformBall.factor_nonnegative
#print axioms OQ14.ConicalUniformBall.norm_bound
#print axioms OQ14.ConicalUniformBall.restricted_difference
