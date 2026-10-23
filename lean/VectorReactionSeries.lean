import VectorReactionTerms

/-! Actual differentiated infinite physical vector reaction series on compact core regions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VectorReactionSeries
open Set Metric OQ14.Maxwell OQ14.SphereHarmonicHilbert OQ14.HarmonicSpatialMajorant
  OQ14.VectorReactionTerms

def series (tm : Bool) (i j : Fin 3) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0<R) (p : Space × Space) : ℂ :=
  ∑' a : TotalIndex,term tm a i j gs R X hR p

theorem actual_derivative_summable (tm : Bool) (i j : Fin 3)
    {gs : List RadialStack.Layer} {R X : ℝ} (hc : RadialStack.Chain gs X R)
    (q M d B : ℝ) (hq : 1≤q) (hM : 0≤M) (hR : 4≤R) (hB : 1≤B)
    (ht : Real.exp 1*B≤R) (hX : X≤2*R) (hd : X-R≤d)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M) (hqp : ∀ g∈gs,g.q≤q)
    (N m : ℕ) (hm : m≤N) (b : ℝ) (hb : 0≤b) (hbB : degreeScale (N+2) b≤B)
    (p : Space × Space) (hp0 : ‖p‖≤b) :
    Summable (fun a : TotalIndex => iteratedFDeriv ℝ m (term tm a i j gs R X (by linarith)) p) := by
  apply Summable.of_norm_bounded
    (PhysicalReactionSeries.indexMajorant (2^N*(DebyeJetBounds.scale N b)^2) q M d B 6)
    (PhysicalReactionSeries.indexMajorant_summable _ q M d B 6 (by positivity) (zero_le_one.trans hB))
  intro a
  exact actual_joint_jet_bound tm a i j hc q M d B hq hM hR hB ht hX hd hp hqp N m hm b hb hbB p hp0

theorem actual_iteratedFDeriv_series (tm : Bool) (i j : Fin 3)
    {gs : List RadialStack.Layer} {R X : ℝ} (hc : RadialStack.Chain gs X R)
    (q M d B : ℝ) (hq : 1≤q) (hM : 0≤M) (hR : 4≤R) (hB : 1≤B)
    (ht : Real.exp 1*B≤R) (hX : X≤2*R) (hd : X-R≤d)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M) (hqp : ∀ g∈gs,g.q≤q)
    (N m : ℕ) (hm : m≤N) (b : ℝ) (hb : 0<b) (hbB : degreeScale (N+2) b≤B)
    (p : Space × Space) (hp0 : ‖p‖<b) :
    iteratedFDeriv ℝ m (series tm i j gs R X (by linarith)) p=
      ∑' a : TotalIndex,iteratedFDeriv ℝ m (term tm a i j gs R X (by linarith)) p := by
  apply LocalSmoothSeries.iteratedFDeriv_tsum_on_open
    (fun a => term tm a i j gs R X (by linarith))
    (fun a => term_smooth tm a i j gs R X (by linarith))
    N (ball 0 b) isOpen_ball (convex_ball (0 : Space × Space) b).isPreconnected
    0 (mem_ball_self hb)
    (fun _ => PhysicalReactionSeries.indexMajorant (2^N*(DebyeJetBounds.scale N b)^2) q M d B 6)
    (fun _ _ => PhysicalReactionSeries.indexMajorant_summable _ q M d B 6 (by positivity) (zero_le_one.trans hB))
    _ m hm p (mem_ball_zero_iff.mpr hp0)
  intro s hs a x hx
  exact actual_joint_jet_bound tm a i j hc q M d B hq hM hR hB ht hX hd hp hqp N s hs b hb.le hbB x
    (mem_ball_zero_iff.mp hx).le

theorem uniform_derivative_series (tm : Bool) (i j : Fin 3)
    {gs : List RadialStack.Layer} {R X : ℝ} (hc : RadialStack.Chain gs X R)
    (q M d B : ℝ) (hq : 1≤q) (hM : 0≤M) (hR : 4≤R) (hB : 1≤B)
    (ht : Real.exp 1*B≤R) (hX : X≤2*R) (hd : X-R≤d)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M) (hqp : ∀ g∈gs,g.q≤q)
    (N m : ℕ) (hm : m≤N) (b : ℝ) (hb : 0<b) (hbB : degreeScale (N+2) b≤B) :
    TendstoUniformlyOn
      (fun s : Finset TotalIndex => fun p : Space × Space =>
        ∑ a∈s,iteratedFDeriv ℝ m (term tm a i j gs R X (by linarith)) p)
      (fun p => iteratedFDeriv ℝ m (series tm i j gs R X (by linarith)) p)
      Filter.atTop (ball 0 b) := by
  have hu := PhysicalReactionSeries.indexMajorant_summable
    (2^N*(DebyeJetBounds.scale N b)^2) q M d B 6 (by positivity) (zero_le_one.trans hB)
  have h := tendstoUniformlyOn_tsum hu
    (fun a p (hp0 : p∈ball (0 : Space × Space) b) =>
      actual_joint_jet_bound tm a i j hc q M d B hq hM hR hB ht hX hd hp hqp N m hm b hb.le hbB p
        (mem_ball_zero_iff.mp hp0).le)
  apply h.congr_right
  intro p hp0
  exact (actual_iteratedFDeriv_series tm i j hc q M d B hq hM hR hB ht hX hd hp hqp N m hm b hb hbB p
    (mem_ball_zero_iff.mp hp0)).symm

end OQ14.VectorReactionSeries
#print axioms OQ14.VectorReactionSeries.actual_derivative_summable
#print axioms OQ14.VectorReactionSeries.actual_iteratedFDeriv_series
#print axioms OQ14.VectorReactionSeries.uniform_derivative_series
