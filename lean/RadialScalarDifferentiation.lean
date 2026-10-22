import RadialScalarUniform

/-! Genuine differentiation of the summed actual scalar reaction series. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialScalarDifferentiation

open Filter Set Metric OQ14.RadialStack OQ14.RadialEntireReaction OQ14.RiccatiOriginSeries
open OQ14.RiccatiCompactDerivatives
open scoped Topology

def series (k m n : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (z w : ℂ) : ℂ :=
  ∑' l : ℕ, ((l+1 : ℝ)^k) • component l m n gs R X hR z w

theorem component_hasDerivAt_left (l m n : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R)
    (z w : ℂ) : HasDerivAt (fun u : ℂ => component l m n gs R X hR u w)
      (component l (m+1) n gs R X hR z w) z := by
  have hd := ((entire_origin l).differentiable_iteratedDeriv m
    (by exact_mod_cast ENat.coe_lt_top m) z).hasDerivAt
  rw [← iteratedDeriv_succ] at hd
  exact (hd.const_mul (RadialSource.gamma l gs R X hR)).mul_const (iteratedDeriv n (origin l) w)

theorem series_swap (k m n : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (z w : ℂ) :
    series k m n gs R X hR z w = series k n m gs R X hR w z := by
  apply tsum_congr
  intro l
  congr 1
  dsimp [component]
  ring

theorem series_hasDerivAt_left (k m n : ℕ) {gs : List Layer} {R X : ℝ}
    (hc : Chain gs X R) (q M d s b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hs : 0 < s) (hb : 0 < b) (ht : Real.exp 1*b ≤ R)
    (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (hmb : s+(m+1 : ℕ) ≤ b) (z w : ℂ) (hz : ‖z‖ < s) (hw : ‖w‖+(n : ℝ) ≤ b) :
    HasDerivAt (fun u : ℂ => series k m n gs R X (by linarith) u w)
      (series k (m+1) n gs R X (by linarith) z w) z := by
  have hRp : 0 < R := by linarith
  unfold series
  apply hasDerivAt_tsum_of_isPreconnected
    (g := fun l (u : ℂ) => ((l+1 : ℝ)^k) • component l m n gs R X hRp u w)
    (g' := fun l (u : ℂ) => ((l+1 : ℝ)^k) • component l (m+1) n gs R X hRp u w)
    (y₀ := (0 : ℂ)) (y := z)
    (u := RadialFullMajorant.majorant q M d b k)
    (RadialFullMajorant.majorant_summable q M d b k hb.le)
    isOpen_ball (convex_ball (0 : ℂ) s).isPreconnected
  · intro l u _
    exact (component_hasDerivAt_left l m n gs R X hRp u w).const_smul ((l+1 : ℝ)^k)
  · intro l u hu
    have hnu : ‖u‖ < s := mem_ball_zero_iff.mp hu
    have hh := RadialFullMajorant.component_weighted_bound l k (m+1) n hc q M d b hq hM hR hb ht hX hd hp hqp
      u w (by linarith) hw
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (l+1 : ℝ)^k)] using hh
  · exact mem_ball_self hs
  · exact RadialFullMajorant.actual_complex_series_summable k m n hc q M d b hq hM hR hb ht hX hd hp hqp
      0 w (by simp only [norm_zero,zero_add]; push_cast at hmb; linarith) hw
  · exact mem_ball_zero_iff.mpr hz

theorem series_hasDerivAt_right (k m n : ℕ) {gs : List Layer} {R X : ℝ}
    (hc : Chain gs X R) (q M d s b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hs : 0 < s) (hb : 0 < b) (ht : Real.exp 1*b ≤ R)
    (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (hnb : s+(n+1 : ℕ) ≤ b) (z w : ℂ) (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖ < s) :
    HasDerivAt (fun v : ℂ => series k m n gs R X (by linarith) z v)
      (series k m (n+1) gs R X (by linarith) z w) w := by
  have hRp : 0 < R := by linarith
  have h := series_hasDerivAt_left k n m hc q M d s b hq hM hR hs hb ht hX hd hp hqp hnb w z hw hz
  have h' := h.congr_deriv (series_swap k (n+1) m gs R X hRp w z)
  exact h'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun v => series_swap k m n gs R X hRp z v))

theorem left_iteratedDeriv_eq (k n : ℕ) {gs : List Layer} {R X : ℝ}
    (hc : Chain gs X R) (q M d s b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hs : 0 < s) (hb : 0 < b) (ht : Real.exp 1*b ≤ R)
    (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (w : ℂ) (hw : ‖w‖+(n : ℝ) ≤ b) :
    ∀ m : ℕ, s+(m : ℝ) ≤ b → ∀ z : ℂ, ‖z‖ < s →
      iteratedDeriv m (fun u : ℂ => series k 0 n gs R X (by linarith) u w) z =
        series k m n gs R X (by linarith) z w := by
  intro m
  induction m with
  | zero => intro _ z _; simp only [iteratedDeriv_zero]
  | succ m ih =>
    intro hmb z hz
    have hm : s+(m : ℝ) ≤ b := by push_cast at hmb; linarith
    have heq : (fun u : ℂ => iteratedDeriv m (fun v : ℂ => series k 0 n gs R X (by linarith) v w) u) =ᶠ[𝓝 z]
        fun u : ℂ => series k m n gs R X (by linarith) u w := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz)] with u hu
      exact ih hm u (mem_ball_zero_iff.mp hu)
    rw [iteratedDeriv_succ]
    rw [heq.deriv_eq]
    exact (series_hasDerivAt_left k m n hc q M d s b hq hM hR hs hb ht hX hd hp hqp hmb z w hz hw).deriv

theorem right_iteratedDeriv_eq (k m : ℕ) {gs : List Layer} {R X : ℝ}
    (hc : Chain gs X R) (q M d s b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hs : 0 < s) (hb : 0 < b) (ht : Real.exp 1*b ≤ R)
    (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (z : ℂ) (hz : ‖z‖+(m : ℝ) ≤ b) :
    ∀ n : ℕ, s+(n : ℝ) ≤ b → ∀ w : ℂ, ‖w‖ < s →
      iteratedDeriv n (fun v : ℂ => series k m 0 gs R X (by linarith) z v) w =
        series k m n gs R X (by linarith) z w := by
  intro n hnb w hw
  have hRp : 0 < R := by linarith
  have he : (fun v : ℂ => series k m 0 gs R X hRp z v) =
      fun v : ℂ => series k 0 m gs R X hRp v z :=
    funext (fun v => series_swap k m 0 gs R X hRp z v)
  rw [he]
  exact (left_iteratedDeriv_eq k m hc q M d s b hq hM hR hs hb ht hX hd hp hqp z hz n hnb w hw).trans
    (series_swap k n m gs R X hRp w z)

theorem mixed_iteratedDeriv_eq (k m n : ℕ) {gs : List Layer} {R X : ℝ}
    (hc : Chain gs X R) (q M d s t b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hs : 0 < s) (ht' : 0 < t) (hb : 0 < b) (ht : Real.exp 1*b ≤ R)
    (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (hmb : s+(m : ℝ) ≤ b) (hnb : t+(n : ℝ) ≤ b)
    (z w : ℂ) (hz : ‖z‖ < s) (hw : ‖w‖ < t) :
    iteratedDeriv n (fun v : ℂ => iteratedDeriv m
      (fun u : ℂ => series k 0 0 gs R X (by linarith) u v) z) w =
        series k m n gs R X (by linarith) z w := by
  have hRp : 0 < R := by linarith
  have htB : t ≤ b := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have heq : (fun v : ℂ => iteratedDeriv m (fun u : ℂ => series k 0 0 gs R X hRp u v) z) =ᶠ[𝓝 w]
      fun v : ℂ => series k m 0 gs R X hRp z v := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hw)] with v hv
    have hvb : ‖v‖+(0 : ℝ) ≤ b := by linarith [mem_ball_zero_iff.mp hv]
    exact left_iteratedDeriv_eq k 0 hc q M d s b hq hM hR hs hb ht hX hd hp hqp v
      (by simpa only [Nat.cast_zero] using hvb) m hmb z hz
  exact (heq.iteratedDeriv_eq n).trans
    (right_iteratedDeriv_eq k m hc q M d t b hq hM hR ht' hb ht hX hd hp hqp z
      (by linarith) n hnb w hw)

theorem series_eq_actual_reaction (k : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R)
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    series k 0 0 gs R X hR (x : ℂ) (y : ℂ) =
      ∑' l : ℕ, ((l+1 : ℝ)^k) • RadialReactionKernel.reaction l gs R X hR x y := by
  apply tsum_congr
  intro l
  congr 1
  change RadialEntireReaction.reaction l gs R X hR (x : ℂ) (y : ℂ) = _
  exact reaction_eq_actual l gs R X hR x y hx hy

theorem eventually_map_eq_actual_mixed (gs : List OQ14.RadialFiniteLimit.Segment)
    (q M s b : ℝ) (k m n : ℕ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hs : 0 ≤ s) (hb : 0 < b)
    (hmb : s+1+(m : ℝ) ≤ b) (hnb : s+1+(n : ℝ) ≤ b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    ∀ᶠ j : ℕ in atTop, ∀ p : OQ14.RadialScalarUniform.Region s,
      (∑' l : ℕ, OQ14.RadialScalarUniform.actualMap gs k m n s j l) p =
        iteratedDeriv n (fun v : ℂ => iteratedDeriv m (fun u : ℂ =>
          series k 0 0 (OQ14.RadialFiniteLimit.layers gs (OQ14.RadialPhaseLimit.radius j)
            (OQ14.RadialPhaseLimit.radius_pos j)) (OQ14.RadialPhaseLimit.radius j)
            (OQ14.RadialPhaseLimit.radius j+OQ14.RadialFiniteLimit.width gs)
            (OQ14.RadialPhaseLimit.radius_pos j) u v) p.val.1) p.val.2 := by
  open OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit OQ14.RadialScalarUniform in
  have hsum := eventually_actual_summable gs q M s b k m n hq hM hb
    (by linarith) (by linarith) hp
  filter_upwards [hsum, OQ14.RadialPhaseLimit.radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    OQ14.RadialPhaseLimit.radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1*b)),
    OQ14.RadialPhaseLimit.radius_tendsto.eventually (eventually_ge_atTop (OQ14.RadialFiniteLimit.width gs))]
      with j hj hR ht hd
  intro p
  have heval := (ContinuousMap.evalCLM ℂ p).map_tsum hj
  have heq : (∑' l : ℕ, OQ14.RadialScalarUniform.actualMap gs k m n s j l) p =
      series k m n (OQ14.RadialFiniteLimit.layers gs (OQ14.RadialPhaseLimit.radius j)
        (OQ14.RadialPhaseLimit.radius_pos j)) (OQ14.RadialPhaseLimit.radius j)
        (OQ14.RadialPhaseLimit.radius j+OQ14.RadialFiniteLimit.width gs)
        (OQ14.RadialPhaseLimit.radius_pos j) p.val.1 p.val.2 := by
    simpa only [ContinuousMap.evalCLM_apply,OQ14.RadialScalarUniform.actualMap_apply,
      OQ14.RadialScalarSeries.actualTerm,series] using heval
  rw [heq]
  have hparams := OQ14.RadialScalarSeries.layers_bounds gs (OQ14.RadialPhaseLimit.radius j)
    (OQ14.RadialPhaseLimit.radius_pos j) q M hp
  apply Eq.symm
  exact mixed_iteratedDeriv_eq k m n
    (OQ14.RadialFiniteLimit.layers_chain gs (OQ14.RadialPhaseLimit.radius j) (OQ14.RadialPhaseLimit.radius_pos j))
    q M (OQ14.RadialFiniteLimit.width gs) (s+1) (s+1) b hq hM hR (by linarith) (by linarith) hb ht
    (by linarith) (by linarith)
    (fun g hg => ⟨(hparams g hg).1,(hparams g hg).2.1,(hparams g hg).2.2.1⟩)
    (fun g hg => (hparams g hg).2.2.2) hmb hnb p.val.1 p.val.2
    (by linarith [OQ14.RadialScalarUniform.left_norm s p])
    (by linarith [OQ14.RadialScalarUniform.right_norm s p])

end OQ14.RadialScalarDifferentiation

#print axioms OQ14.RadialScalarDifferentiation.component_hasDerivAt_left
#print axioms OQ14.RadialScalarDifferentiation.series_swap
#print axioms OQ14.RadialScalarDifferentiation.series_hasDerivAt_left
#print axioms OQ14.RadialScalarDifferentiation.series_hasDerivAt_right
#print axioms OQ14.RadialScalarDifferentiation.left_iteratedDeriv_eq
#print axioms OQ14.RadialScalarDifferentiation.right_iteratedDeriv_eq
#print axioms OQ14.RadialScalarDifferentiation.mixed_iteratedDeriv_eq
#print axioms OQ14.RadialScalarDifferentiation.series_eq_actual_reaction
#print axioms OQ14.RadialScalarDifferentiation.eventually_map_eq_actual_mixed
