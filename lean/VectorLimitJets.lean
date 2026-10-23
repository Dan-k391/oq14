import VectorLimitIdentification

/-! Genuine differentiated identification of the central-inversion limit kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VectorLimitJets
open Filter Set Metric Complex OQ14.Maxwell OQ14.SphereHarmonicHilbert
  OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit OQ14.HarmonicSpatialMajorant
  OQ14.VectorReactionTerms OQ14.VectorLimitIdentification
open PhysicalReactionLimit (Region Jet region_norm)
open scoped Topology

theorem limitTerm_smooth (tm : Bool) (i j : Fin 3) (gs : List Segment) (a : TotalIndex) :
    ContDiff ℝ (⊤ : ℕ∞) (limitTerm tm i j gs a) :=
  contDiff_const.mul (product_smooth tm a i j)

theorem limitMap_apply (tm : Bool) (i j : Fin 3) (gs : List Segment) (m : ℕ) (b : ℝ)
    (a : TotalIndex) (p : Region b) :
    VectorReactionLimit.limitMap tm i j gs m b a p=
      iteratedFDeriv ℝ m (limitTerm tm i j gs a) p.val := by
  have he : limitTerm tm i j gs a=
      ((-((limitingCoefficients a.1 gs).1/(limitingCoefficients a.1 gs).2+I))*(angularWeight a.1 : ℂ)) •
        product tm a i j := rfl
  rw [he,iteratedFDeriv_const_smul_apply
    ((product_smooth tm a i j).contDiffAt.of_le (by exact_mod_cast le_top))]
  simp only [VectorReactionLimit.limitMap,VectorReactionLimit.basisJetMap,
    ContinuousMap.smul_apply,ContinuousMap.coe_mk,smul_smul]

def bound (q M : ℝ) (gs : List Segment) (m : ℕ) (b : ℝ) : TotalIndex → ℝ :=
  PhysicalReactionSeries.indexMajorant (2^m*(DebyeJetBounds.scale m b)^2)
    q M (width gs) (max 1 (degreeScale (m+2) b)) 6

theorem bound_summable (q M : ℝ) (gs : List Segment) (m : ℕ) (b : ℝ) :
    Summable (bound q M gs m b) :=
  PhysicalReactionSeries.indexMajorant_summable _ q M (width gs) _ 6
    (by positivity) (zero_le_one.trans (le_max_left _ _))

theorem limitMap_bound (tm : Bool) (i j : Fin 3) (gs : List Segment)
    (q M b : ℝ) (m : ℕ) (hq : 1≤q) (hM : 0≤M) (hb : 0≤b)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M ∧ g.q≤q) (a : TotalIndex) :
    ‖VectorReactionLimit.limitMap tm i j gs m b a‖≤bound q M gs m b a := by
  have hn : Tendsto (fun n => ‖VectorReactionLimit.actualMap tm i j gs m b n a‖) atTop
      (𝓝 ‖VectorReactionLimit.limitMap tm i j gs m b a‖) :=
    (continuous_norm.tendsto (VectorReactionLimit.limitMap tm i j gs m b a)).comp
      (VectorReactionLimit.actualMap_tendsto tm i j gs m b a)
  apply le_of_tendsto hn
  filter_upwards [VectorReactionLimit.eventually_map_majorant tm i j gs q M b
    (max 1 (degreeScale (m+2) b)) m hq hM hb (le_max_left _ _) (le_max_right _ _) hp] with n hn
  exact hn a

theorem limitTerm_jet_bound (tm : Bool) (i j : Fin 3) (gs : List Segment)
    (q M b : ℝ) (m : ℕ) (hq : 1≤q) (hM : 0≤M) (hb : 0≤b)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M ∧ g.q≤q) (a : TotalIndex)
    (p : Space × Space) (hp0 : ‖p‖≤b) :
    ‖iteratedFDeriv ℝ m (limitTerm tm i j gs a) p‖≤bound q M gs m b a := by
  let v : Region b := ⟨p,mem_closedBall_zero_iff.mpr hp0⟩
  rw [← limitMap_apply tm i j gs m b a v]
  exact ((VectorReactionLimit.limitMap tm i j gs m b a).norm_coe_le_norm v).trans
    (limitMap_bound tm i j gs q M b m hq hM hb hp a)

theorem derivative_summable (tm : Bool) (i j : Fin 3) (gs : List Segment)
    (q M b : ℝ) (m : ℕ) (hq : 1≤q) (hM : 0≤M) (hb : 0≤b)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M ∧ g.q≤q)
    (p : Space × Space) (hp0 : ‖p‖≤b) :
    Summable (fun a => iteratedFDeriv ℝ m (limitTerm tm i j gs a) p) :=
  Summable.of_norm_bounded (bound q M gs m b) (bound_summable q M gs m b)
    (fun a => limitTerm_jet_bound tm i j gs q M b m hq hM hb hp a p hp0)

theorem paired_derivative_series (q : ℝ) (hq : 1≤q) (n m : ℕ) (i j : Fin 3)
    (b : ℝ) (hb : 0<b) (p : Space × Space) (hp0 : ‖p‖<b) :
    iteratedFDeriv ℝ m (kernel q n i j) p=
      ∑' a : TotalIndex,iteratedFDeriv ℝ m
        (fun z => combinedTerm q (zero_lt_one.trans_le hq) n i j z a) p := by
  let te := RadialPairedFamily.te q (zero_lt_one.trans_le hq) n
  let tm := RadialPairedFamily.tm q (zero_lt_one.trans_le hq) n
  have hq2 : 1≤q^2 := by nlinarith
  have hte := RadialPairedFamily.pairs_parameters q 1 hq le_rfl hq2 n
  have htm := RadialPairedFamily.pairs_parameters q (q^2) hq hq2 le_rfl n
  have he : kernel q n i j=(fun z => ∑' a,combinedTerm q (zero_lt_one.trans_le hq) n i j z a) :=
    funext (fun z => (total_paired_expansion q (zero_lt_one.trans_le hq) n i j z).tsum_eq.symm)
  rw [he]
  apply LocalSmoothSeries.iteratedFDeriv_tsum_on_open
    (fun a z => combinedTerm q (zero_lt_one.trans_le hq) n i j z a)
    (fun a => (limitTerm_smooth true i j tm a).add (limitTerm_smooth false i j te a))
    m (ball 0 b) isOpen_ball (convex_ball (0 : Space × Space) b).isPreconnected
    0 (mem_ball_self hb)
    (fun s a => bound q (q^2) tm s b a+bound q (q^2) te s b a)
    (fun s _ => (bound_summable q (q^2) tm s b).add (bound_summable q (q^2) te s b))
    _ m le_rfl p (mem_ball_zero_iff.mpr hp0)
  intro s hs a x hx
  change ‖iteratedFDeriv ℝ s (limitTerm true i j tm a+limitTerm false i j te a) x‖≤_
  rw [iteratedFDeriv_add_apply
    ((limitTerm_smooth true i j tm a).contDiffAt.of_le (by exact_mod_cast le_top))
    ((limitTerm_smooth false i j te a).contDiffAt.of_le (by exact_mod_cast le_top))]
  exact (norm_add_le _ _).trans (add_le_add
    (limitTerm_jet_bound true i j tm q (q^2) b s hq (sq_nonneg q) hb.le htm a x (mem_ball_zero_iff.mp hx).le)
    (limitTerm_jet_bound false i j te q (q^2) b s hq (sq_nonneg q) hb.le hte a x (mem_ball_zero_iff.mp hx).le))

end OQ14.VectorLimitJets

#print axioms OQ14.VectorLimitJets.limitTerm_smooth
#print axioms OQ14.VectorLimitJets.limitMap_apply
#print axioms OQ14.VectorLimitJets.bound_summable
#print axioms OQ14.VectorLimitJets.limitMap_bound
#print axioms OQ14.VectorLimitJets.limitTerm_jet_bound
#print axioms OQ14.VectorLimitJets.derivative_summable
#print axioms OQ14.VectorLimitJets.paired_derivative_series
