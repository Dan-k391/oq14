import VectorLimitIdentification

/-! Exact positive-degree indexing of the actual reaction series and all its derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OQ14.VectorReactionPositive
open Set Metric OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.SphereHarmonicHilbert
open OQ14.VectorHarmonicNormalization OQ14.VectorReactionTerms OQ14.HarmonicSpatialMajorant
open OQ14.VectorLimitIdentification (positive positive_hasSum_iff)

theorem summable_positive_iff {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : TotalIndex → E) (hzero : ∀ a : Index 0,f ⟨0,a⟩=0) :
    Summable (fun a => f (positive a)) ↔ Summable f := by
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨s,(positive_hasSum_iff f hzero s).mp hs⟩
  · rintro ⟨s,hs⟩
    exact ⟨s,(positive_hasSum_iff f hzero s).mpr hs⟩

theorem tsum_positive_eq {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [T2Space E]
    (f : TotalIndex → E) (hzero : ∀ a : Index 0,f ⟨0,a⟩=0) :
    (∑' a, f (positive a))=∑' a,f a := by
  by_cases hf : Summable f
  · exact ((positive_hasSum_iff f hzero _).mpr hf.hasSum).tsum_eq
  · rw [tsum_eq_zero_of_not_summable hf,
      tsum_eq_zero_of_not_summable (fun hp => hf ((summable_positive_iff f hzero).mp hp))]

theorem term_zero (tm : Bool) (i j : Fin 3) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0<R) (a : Index 0) : term tm ⟨0,a⟩ i j gs R X hR=0 := by
  simp only [term,angularWeight,Nat.cast_zero,zero_mul,inv_zero,Complex.ofReal_zero,mul_zero,zero_smul]

theorem derivative_zero (tm : Bool) (i j : Fin 3) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0<R) (a : Index 0) (m : ℕ) (p : Space × Space) :
    iteratedFDeriv ℝ m (term tm ⟨0,a⟩ i j gs R X hR) p=0 := by
  rw [term_zero]
  change iteratedFDeriv ℝ m (fun _ : Space × Space => (0 : ℂ)) p=0
  rw [iteratedFDeriv_zero_fun]
  rfl

theorem positive_tsum_eq_series (tm : Bool) (i j : Fin 3) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0<R) (p : Space × Space) :
    (∑' a : PositiveIndex,term tm (positive a) i j gs R X hR p)=
      VectorReactionSeries.series tm i j gs R X hR p :=
  tsum_positive_eq (fun a : TotalIndex => term tm a i j gs R X hR p)
    (fun a => congrFun (term_zero tm i j gs R X hR a) p)

theorem positive_derivative_tsum_eq (tm : Bool) (i j : Fin 3) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0<R) (m : ℕ) (p : Space × Space) :
    (∑' a : PositiveIndex,iteratedFDeriv ℝ m (term tm (positive a) i j gs R X hR) p)=
      ∑' a : TotalIndex,iteratedFDeriv ℝ m (term tm a i j gs R X hR) p :=
  tsum_positive_eq (fun a : TotalIndex => iteratedFDeriv ℝ m (term tm a i j gs R X hR) p)
    (fun a => derivative_zero tm i j gs R X hR a m p)

theorem actual_positive_derivative_summable (tm : Bool) (i j : Fin 3)
    {gs : List RadialStack.Layer} {R X : ℝ} (hc : RadialStack.Chain gs X R)
    (q M d B : ℝ) (hq : 1≤q) (hM : 0≤M) (hR : 4≤R) (hB : 1≤B)
    (ht : Real.exp 1*B≤R) (hX : X≤2*R) (hd : X-R≤d)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M) (hqp : ∀ g∈gs,g.q≤q)
    (N m : ℕ) (hm : m≤N) (b : ℝ) (hb : 0≤b) (hbB : degreeScale (N+2) b≤B)
    (p : Space × Space) (hp0 : ‖p‖≤b) :
    Summable (fun a : PositiveIndex => iteratedFDeriv ℝ m
      (term tm (positive a) i j gs R X (by linarith)) p) :=
  (summable_positive_iff _ (fun a => derivative_zero tm i j gs R X (by linarith) a m p)).mpr
    (VectorReactionSeries.actual_derivative_summable tm i j hc q M d B hq hM hR hB ht hX hd hp hqp
      N m hm b hb hbB p hp0)

theorem actual_positive_hasSum (tm : Bool) (i j : Fin 3)
    {gs : List RadialStack.Layer} {R X : ℝ} (hc : RadialStack.Chain gs X R)
    (q M d B : ℝ) (hq : 1≤q) (hM : 0≤M) (hR : 4≤R) (hB : 1≤B)
    (ht : Real.exp 1*B≤R) (hX : X≤2*R) (hd : X-R≤d)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M) (hqp : ∀ g∈gs,g.q≤q)
    (N : ℕ) (b : ℝ) (hb : 0≤b) (hbB : degreeScale (N+2) b≤B)
    (p : Space × Space) (hp0 : ‖p‖≤b) :
    HasSum (fun a : PositiveIndex => term tm (positive a) i j gs R X (by linarith) p)
      (VectorReactionSeries.series tm i j gs R X (by linarith) p) := by
  have h := actual_positive_derivative_summable tm i j hc q M d B hq hM hR hB ht hX hd hp hqp
    N 0 (Nat.zero_le _) b hb hbB p hp0
  have hz := h.hasSum.mapL
    (continuousMultilinearCurryFin0 ℝ (Space × Space) ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  have hs : Summable (fun a : PositiveIndex => term tm (positive a) i j gs R X (by linarith) p) := by
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_apply,
      ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply] using hz.summable
  simpa only [positive_tsum_eq_series] using hs.hasSum

theorem actual_positive_derivative_hasSum (tm : Bool) (i j : Fin 3)
    {gs : List RadialStack.Layer} {R X : ℝ} (hc : RadialStack.Chain gs X R)
    (q M d B : ℝ) (hq : 1≤q) (hM : 0≤M) (hR : 4≤R) (hB : 1≤B)
    (ht : Real.exp 1*B≤R) (hX : X≤2*R) (hd : X-R≤d)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M) (hqp : ∀ g∈gs,g.q≤q)
    (N m : ℕ) (hm : m≤N) (b : ℝ) (hb : 0<b) (hbB : degreeScale (N+2) b≤B)
    (p : Space × Space) (hp0 : ‖p‖<b) :
    HasSum (fun a : PositiveIndex => iteratedFDeriv ℝ m
      (term tm (positive a) i j gs R X (by linarith)) p)
      (iteratedFDeriv ℝ m (VectorReactionSeries.series tm i j gs R X (by linarith)) p) := by
  have h := VectorReactionSeries.actual_derivative_summable tm i j hc q M d B hq hM hR hB ht hX hd hp hqp
    N m hm b hb.le hbB p hp0.le
  rw [VectorReactionSeries.actual_iteratedFDeriv_series tm i j hc q M d B hq hM hR hB ht hX hd hp hqp
    N m hm b hb hbB p hp0]
  exact (positive_hasSum_iff _ (fun a => derivative_zero tm i j gs R X (by linarith) a m p) _).mpr h.hasSum

end OQ14.VectorReactionPositive

#print axioms OQ14.VectorReactionPositive.summable_positive_iff
#print axioms OQ14.VectorReactionPositive.tsum_positive_eq
#print axioms OQ14.VectorReactionPositive.term_zero
#print axioms OQ14.VectorReactionPositive.derivative_zero
#print axioms OQ14.VectorReactionPositive.positive_tsum_eq_series
#print axioms OQ14.VectorReactionPositive.positive_derivative_tsum_eq
#print axioms OQ14.VectorReactionPositive.actual_positive_derivative_summable
#print axioms OQ14.VectorReactionPositive.actual_positive_hasSum
#print axioms OQ14.VectorReactionPositive.actual_positive_derivative_hasSum
