import SpatialReactionTerms
import LocalSmoothSeries

/-! Genuine spatial differentiation of the normalized finite-stack scalar series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.SpatialReactionSeries
open Set Metric OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.HarmonicSpatialMajorant
  OQ14.SpatialReactionMajorant OQ14.SpatialReactionTerms

def indexMajorant (C q M d B : ℝ) (k : ℕ) (a : SphereHarmonicHilbert.TotalIndex) : ℝ :=
  C*RadialFullMajorant.majorant q M d B k a.1

theorem indexMajorant_summable (C q M d B : ℝ) (k : ℕ) (hC : 0 ≤ C) (hB : 0 ≤ B) :
    Summable (indexMajorant C q M d B k) := by
  apply (summable_sigma_of_nonneg (fun a => mul_nonneg hC
    (RadialFullMajorant.majorant_nonnegative _ _ _ _ _ _))).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable,?_⟩
  simp only [tsum_fintype,indexMajorant,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply Summable.of_nonneg_of_le (fun l => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg hC (RadialFullMajorant.majorant_nonnegative _ _ _ _ _ _)))
    (f := fun l => C*RadialFullMajorant.majorant q M d B (k+3) l)
  · intro l
    have hcard : (Fintype.card (Index l) : ℝ) ≤ (l+1 : ℝ)^3 := by
      simp only [Index,Fintype.card_fin]
      exact_mod_cast SphereHarmonicDimension.harmonicSpace_finrank_le l
    rw [majorant_weight_shift]
    have hprod := mul_le_mul_of_nonneg_right hcard
      (mul_nonneg hC (RadialFullMajorant.majorant_nonnegative q M d B k l))
    convert hprod using 1; ring
  · exact (RadialFullMajorant.majorant_summable q M d B (k+3) hB).mul_left C

def series (gs : List RadialStack.Layer) (R X : ℝ) (hR : 0 < R) (u v : ℂ)
    (p : Space × Space) : ℂ := ∑' a : SphereHarmonicHilbert.TotalIndex,term a gs R X hR u v p

theorem actual_iteratedFDeriv_series {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (u v : ℂ) (N j : ℕ) (hj : j ≤ N) (b : ℝ) (hb : 0 < b)
    (hbB : degreeScale N b ≤ B) (p : Space × Space) (hp0 : ‖p‖ < b) :
    iteratedFDeriv ℝ j (series gs R X (by linarith) u v) p=
      ∑' a : SphereHarmonicHilbert.TotalIndex,iteratedFDeriv ℝ j (term a gs R X (by linarith) u v) p := by
  let C := 2^N*(lowerJetScale u N b*lowerJetScale v N b)
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (mul_nonneg (lowerJetScale_nonnegative u N b hb.le) (lowerJetScale_nonnegative v N b hb.le))
  apply LocalSmoothSeries.iteratedFDeriv_tsum_on_open
    (fun a => term a gs R X (by linarith) u v) (fun a => term_smooth a gs R X (by linarith) u v)
    N (Metric.ball 0 b) isOpen_ball (convex_ball (0 : Space × Space) b).isPreconnected
    0 (Metric.mem_ball_self hb) (fun _ => indexMajorant C q M d B 6)
    (fun _ _ => indexMajorant_summable C q M d B 6 hC (zero_le_one.trans hB))
    _ j hj p (mem_ball_zero_iff.mpr hp0)
  intro k hk a x hx
  exact actual_joint_jet_bound a hc q M d B hq hM hR hB ht hX hd hp hqp
    u v N k hk b hb.le hbB x (mem_ball_zero_iff.mp hx).le

end OQ14.SpatialReactionSeries

#print axioms OQ14.SpatialReactionSeries.indexMajorant_summable

#print axioms OQ14.SpatialReactionSeries.actual_iteratedFDeriv_series
