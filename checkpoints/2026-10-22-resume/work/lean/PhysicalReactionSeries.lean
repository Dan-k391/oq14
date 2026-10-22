import PhysicalScalarReaction
import SpatialReactionSeries

/-! Actual compact spatial differentiation for the physical scalar reaction coefficient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.PhysicalReactionSeries
open Complex Set Metric OQ14.Maxwell OQ14.HarmonicSpatialMajorant OQ14.SpatialReactionTerms
  OQ14.SpatialReactionMajorant OQ14.RiccatiSeriesCoefficients

theorem free_weighted_amplitude_bound (l k : ℕ) (B : ℝ) (hB : 1 ≤ B) :
    (l+1 : ℝ)^k*(amplitude l 0)^2*B^(2*l) ≤
      RadialFullMajorant.majorant 1 0 0 B k l := by
  have hp : 1 ≤ RadialLowTail.prefactor 0 0 B := by
    have he : 1 ≤ Real.exp (B^2) := Real.one_le_exp_iff.mpr (sq_nonneg B)
    dsimp [RadialLowTail.prefactor,RadialLowTail.bound]
    norm_num
    nlinarith
  have hpow := pow_le_pow_right₀ hB (show 2*l ≤ 2*(l+1) by omega)
  have hlow : (l+1 : ℝ)^k*(amplitude l 0)^2*B^(2*l) ≤ RadialLowTail.majorant B k l := by
    have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (l+1 : ℝ)^k*(amplitude l 0)^2)
    convert hh using 1; simp only [RadialLowTail.majorant]; ring
  have hlow0 := RadialLowTail.majorant_nonnegative B k l
  have hm := RadialMiddleTail.majorant_nonnegative 1 B k l
  have hmid : 0 ≤ RadialMiddleTail.prefactor 1 0 0 B*RadialMiddleTail.majorant 1 B k l := by
    dsimp [RadialMiddleTail.prefactor]
    positivity
  have hhigh : 0 ≤ (4*B^2*Real.exp (2*B^2))*((l+1 : ℝ)^k*(1/2 : ℝ)^l) := by positivity
  dsimp only [RadialFullMajorant.majorant]
  nlinarith [mul_le_mul_of_nonneg_right hp hlow0]

def radialMajorant (q M d B : ℝ) (k l : ℕ) : ℝ :=
  RadialFullMajorant.majorant q M d B k l+RadialFullMajorant.majorant 1 0 0 B k l

theorem physical_amplitude_bound (l k : ℕ) {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q) :
    (l+1 : ℝ)^k*‖-(RadialSource.gamma l gs R X (by linarith)+I)‖*(amplitude l 0)^2*B^(2*l) ≤
      radialMajorant q M d B k l := by
  have hγ := RiccatiImaginaryBound.gamma_weighted_amplitude_bound l k hc q M d B hq hM hR hB ht hX hd hp hqp
  have hfree := free_weighted_amplitude_bound l k B hB
  have hnorm : ‖-(RadialSource.gamma l gs R X (by linarith)+I)‖ ≤
      ‖RadialSource.gamma l gs R X (by linarith)‖+1 := by
    simpa only [norm_neg,norm_I] using norm_add_le (RadialSource.gamma l gs R X (by linarith)) I
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ (l+1 : ℝ)^k))
      (sq_nonneg (amplitude l 0))) (pow_nonneg (zero_le_one.trans hB) (2*l))
  dsimp only [radialMajorant]
  nlinarith

def indexMajorant (C q M d B : ℝ) (k : ℕ) (a : SphereHarmonicHilbert.TotalIndex) : ℝ :=
  C*radialMajorant q M d B k a.1

theorem indexMajorant_summable (C q M d B : ℝ) (k : ℕ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    Summable (indexMajorant C q M d B k) := by
  change Summable (fun a : SphereHarmonicHilbert.TotalIndex => C*(RadialFullMajorant.majorant q M d B k a.1+RadialFullMajorant.majorant 1 0 0 B k a.1))
  simpa only [SpatialReactionSeries.indexMajorant,mul_add] using
    (SpatialReactionSeries.indexMajorant_summable C q M d B k hC hB).add
      (SpatialReactionSeries.indexMajorant_summable C 1 0 0 B k hC hB)

theorem actual_joint_jet_bound (a : SphereHarmonicHilbert.TotalIndex)
    {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (N j : ℕ) (hj : j ≤ N) (b : ℝ) (hb : 0 ≤ b) (hbB : degreeScale N b ≤ B)
    (p : Space × Space) (hp0 : ‖p‖ ≤ b) :
    ‖iteratedFDeriv ℝ j (PhysicalScalarReaction.term a gs R X (by linarith)) p‖ ≤
      (2^N*(lowerJetScale 1 N b)^2)*radialMajorant q M d B 6 a.1 := by
  rw [PhysicalScalarReaction.term,iteratedFDeriv_const_smul_apply (by
    exact (basisProduct_smooth a 1 1).contDiffAt.of_le (by exact_mod_cast le_top))]
  apply (ContinuousMultilinearMap.opNorm_smul_le _ _).trans
  have hh := mul_le_mul_of_nonneg_left (basisProduct_jet_bound a 1 1 N j hj b B hb hB hbB p hp0)
    (norm_nonneg (-(RadialSource.gamma a.1 gs R X (by linarith)+I)))
  have hrad := physical_amplitude_bound a.1 6 hc q M d B hq hM hR hB ht hX hd hp hqp
  calc
    _ ≤ (2^N*(lowerJetScale 1 N b)^2)*
        ((a.1+1 : ℝ)^6*‖-(RadialSource.gamma a.1 gs R X (by linarith)+I)‖*(amplitude a.1 0)^2*B^(2*a.1)) := by
      convert hh using 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrad (by positivity)

def series (gs : List RadialStack.Layer) (R X : ℝ) (hR : 0 < R) (p : Space × Space) : ℂ :=
  ∑' a : SphereHarmonicHilbert.TotalIndex,PhysicalScalarReaction.term a gs R X hR p

theorem actual_iteratedFDeriv_series {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (N j : ℕ) (hj : j ≤ N) (b : ℝ) (hb : 0 < b) (hbB : degreeScale N b ≤ B)
    (p : Space × Space) (hp0 : ‖p‖ < b) :
    iteratedFDeriv ℝ j (series gs R X (by linarith)) p=
      ∑' a : SphereHarmonicHilbert.TotalIndex,
        iteratedFDeriv ℝ j (PhysicalScalarReaction.term a gs R X (by linarith)) p := by
  apply LocalSmoothSeries.iteratedFDeriv_tsum_on_open
    (fun a => PhysicalScalarReaction.term a gs R X (by linarith))
    (fun a => PhysicalScalarReaction.term_smooth a gs R X (by linarith))
    N (ball 0 b) isOpen_ball (convex_ball (0 : Space × Space) b).isPreconnected
    0 (mem_ball_self hb) (fun _ => indexMajorant (2^N*(lowerJetScale 1 N b)^2) q M d B 6)
    (fun _ _ => indexMajorant_summable _ q M d B 6 (by positivity) (zero_le_one.trans hB))
    _ j hj p (mem_ball_zero_iff.mpr hp0)
  intro k hk a x hx
  exact actual_joint_jet_bound a hc q M d B hq hM hR hB ht hX hd hp hqp N k hk b hb.le hbB x
    (mem_ball_zero_iff.mp hx).le


theorem actual_derivative_summable {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (N j : ℕ) (hj : j ≤ N) (b : ℝ) (hb : 0 ≤ b) (hbB : degreeScale N b ≤ B)
    (p : Space × Space) (hp0 : ‖p‖ ≤ b) :
    Summable (fun a : SphereHarmonicHilbert.TotalIndex =>
      iteratedFDeriv ℝ j (PhysicalScalarReaction.term a gs R X (by linarith)) p) := by
  apply Summable.of_norm_bounded (indexMajorant (2^N*(lowerJetScale 1 N b)^2) q M d B 6)
    (indexMajorant_summable _ q M d B 6 (by positivity) (zero_le_one.trans hB))
  intro a
  exact actual_joint_jet_bound a hc q M d B hq hM hR hB ht hX hd hp hqp N j hj b hb hbB p hp0

theorem uniform_derivative_series {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (N j : ℕ) (hj : j ≤ N) (b : ℝ) (hb : 0 < b) (hbB : degreeScale N b ≤ B) :
    TendstoUniformlyOn
      (fun t : Finset SphereHarmonicHilbert.TotalIndex => fun p : Space × Space =>
        ∑ a ∈ t,iteratedFDeriv ℝ j (PhysicalScalarReaction.term a gs R X (by linarith)) p)
      (fun p => iteratedFDeriv ℝ j (series gs R X (by linarith)) p)
      Filter.atTop (ball 0 b) := by
  have hu := indexMajorant_summable (2^N*(lowerJetScale 1 N b)^2) q M d B 6
    (by positivity) (zero_le_one.trans hB)
  have hh := tendstoUniformlyOn_tsum hu
    (fun a p (hp0 : p∈ball (0 : Space × Space) b) =>
      actual_joint_jet_bound a hc q M d B hq hM hR hB ht hX hd hp hqp N j hj b hb.le hbB p
        (mem_ball_zero_iff.mp hp0).le)
  apply hh.congr_right
  intro p hp0
  exact (actual_iteratedFDeriv_series hc q M d B hq hM hR hB ht hX hd hp hqp N j hj b hb hbB p
    (mem_ball_zero_iff.mp hp0)).symm

end OQ14.PhysicalReactionSeries

#print axioms OQ14.PhysicalReactionSeries.free_weighted_amplitude_bound

#print axioms OQ14.PhysicalReactionSeries.physical_amplitude_bound

#print axioms OQ14.PhysicalReactionSeries.indexMajorant_summable

#print axioms OQ14.PhysicalReactionSeries.actual_joint_jet_bound

#print axioms OQ14.PhysicalReactionSeries.actual_iteratedFDeriv_series

#print axioms OQ14.PhysicalReactionSeries.actual_derivative_summable

#print axioms OQ14.PhysicalReactionSeries.uniform_derivative_series
