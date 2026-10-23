import VectorReactionSeries
import PhysicalReactionLimit

/-! Genuine compact joint-jet limits of the normalized vector reaction mode series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VectorReactionLimit
open Filter Set Metric Complex OQ14.Maxwell OQ14.RadialStack OQ14.RadialFiniteLimit
  OQ14.RadialPhaseLimit OQ14.SphereHarmonicHilbert OQ14.HarmonicSpatialMajorant
  OQ14.VectorReactionTerms
open PhysicalReactionLimit (Region Jet region_norm)
open scoped Topology

def basisJetMap (tm : Bool) (i j : Fin 3) (a : TotalIndex) (m : ℕ) (b : ℝ) : C(Region b,Jet m) where
  toFun p := (angularWeight a.1 : ℂ) • iteratedFDeriv ℝ m (product tm a i j) p.val
  continuous_toFun := continuous_const.smul (((product_smooth tm a i j).continuous_iteratedFDeriv
    (by exact_mod_cast le_top)).comp continuous_subtype_val)

def actualMap (tm : Bool) (i j : Fin 3) (gs : List Segment) (m : ℕ) (b : ℝ) (n : ℕ) (a : TotalIndex) :
    C(Region b,Jet m) :=
  (-(RadialSource.gamma a.1 (layers gs (radius n) (radius_pos n))
    (radius n) (radius n+width gs) (radius_pos n)+I)) • basisJetMap tm i j a m b

def limitMap (tm : Bool) (i j : Fin 3) (gs : List Segment) (m : ℕ) (b : ℝ) (a : TotalIndex) :
    C(Region b,Jet m) :=
  (-((limitingCoefficients a.1 gs).1/(limitingCoefficients a.1 gs).2+I)) • basisJetMap tm i j a m b

theorem actualMap_tendsto (tm : Bool) (i j : Fin 3) (gs : List Segment) (m : ℕ) (b : ℝ) (a : TotalIndex) :
    Tendsto (fun n => actualMap tm i j gs m b n a) atTop (𝓝 (limitMap tm i j gs m b a)) :=
  ((actual_gamma_limit a.1 gs).add_const I).neg.smul_const (basisJetMap tm i j a m b)

theorem actualMap_apply (tm : Bool) (i j : Fin 3) (gs : List Segment) (m : ℕ) (b : ℝ)
    (n : ℕ) (a : TotalIndex) (p : Region b) :
    actualMap tm i j gs m b n a p=
      iteratedFDeriv ℝ m (term tm a i j (layers gs (radius n) (radius_pos n))
        (radius n) (radius n+width gs) (radius_pos n)) p.val := by
  rw [term,iteratedFDeriv_const_smul_apply
    ((product_smooth tm a i j).contDiffAt.of_le (by exact_mod_cast le_top))]
  simp only [actualMap,ContinuousMap.smul_apply,basisJetMap,ContinuousMap.coe_mk,smul_smul]

theorem eventually_map_majorant (tm : Bool) (i j : Fin 3) (gs : List Segment)
    (q M b B : ℝ) (m : ℕ) (hq : 1≤q) (hM : 0≤M) (hb : 0≤b) (hB : 1≤B)
    (hbB : degreeScale (m+2) b≤B)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M ∧ g.q≤q) :
    ∀ᶠ n : ℕ in atTop,∀ a : TotalIndex,
      ‖actualMap tm i j gs m b n a‖≤
        PhysicalReactionSeries.indexMajorant (2^m*(DebyeJetBounds.scale m b)^2) q M (width gs) B 6 a := by
  filter_upwards [radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1*B)),
    radius_tendsto.eventually (eventually_ge_atTop (width gs))] with n hR ht hd
  intro a
  have hrad := RadialFullMajorant.majorant_nonnegative q M (width gs) B 6 a.1
  have hfree := RadialFullMajorant.majorant_nonnegative 1 0 0 B 6 a.1
  have hbound : 0≤PhysicalReactionSeries.indexMajorant (2^m*(DebyeJetBounds.scale m b)^2)
      q M (width gs) B 6 a := by
    dsimp [PhysicalReactionSeries.indexMajorant,PhysicalReactionSeries.radialMajorant]
    positivity
  rw [(actualMap tm i j gs m b n a).norm_le hbound]
  intro p
  rw [actualMap_apply]
  have hparams := RadialScalarSeries.layers_bounds gs (radius n) (radius_pos n) q M hp
  exact actual_joint_jet_bound tm a i j (layers_chain gs (radius n) (radius_pos n))
    q M (width gs) B hq hM hR hB ht (by linarith) (by linarith)
    (fun g hg => ⟨(hparams g hg).1,(hparams g hg).2.1,(hparams g hg).2.2.1⟩)
    (fun g hg => (hparams g hg).2.2.2) m m le_rfl b hb hbB p.val (region_norm b p)

theorem eventually_actual_summable (tm : Bool) (i j : Fin 3) (gs : List Segment)
    (q M b B : ℝ) (m : ℕ) (hq : 1≤q) (hM : 0≤M) (hb : 0≤b) (hB : 1≤B)
    (hbB : degreeScale (m+2) b≤B)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M ∧ g.q≤q) :
    ∀ᶠ n : ℕ in atTop,Summable (actualMap tm i j gs m b n) := by
  filter_upwards [eventually_map_majorant tm i j gs q M b B m hq hM hb hB hbB hp] with n hn
  exact Summable.of_norm_bounded (f := actualMap tm i j gs m b n) _
    (PhysicalReactionSeries.indexMajorant_summable (2^m*(DebyeJetBounds.scale m b)^2)
      q M (width gs) B 6 (by positivity) (zero_le_one.trans hB)) hn

theorem limiting_summable (tm : Bool) (i j : Fin 3) (gs : List Segment)
    (q M b B : ℝ) (m : ℕ) (hq : 1≤q) (hM : 0≤M) (hb : 0≤b) (hB : 1≤B)
    (hbB : degreeScale (m+2) b≤B)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M ∧ g.q≤q) :
    Summable (limitMap tm i j gs m b) := by
  apply Summable.of_norm_bounded (f := limitMap tm i j gs m b) _
    (PhysicalReactionSeries.indexMajorant_summable (2^m*(DebyeJetBounds.scale m b)^2)
      q M (width gs) B 6 (by positivity) (zero_le_one.trans hB))
  intro a
  have hn : Tendsto (fun n => ‖actualMap tm i j gs m b n a‖) atTop (𝓝 ‖limitMap tm i j gs m b a‖) :=
    (continuous_norm.tendsto (limitMap tm i j gs m b a)).comp (actualMap_tendsto tm i j gs m b a)
  apply le_of_tendsto hn
  filter_upwards [eventually_map_majorant tm i j gs q M b B m hq hM hb hB hbB hp] with n hn
  exact hn a

theorem uniform_physical_jet_limit (tm : Bool) (i j : Fin 3) (gs : List Segment)
    (q M b B : ℝ) (m : ℕ) (hq : 1≤q) (hM : 0≤M) (hb : 0≤b) (hB : 1≤B)
    (hbB : degreeScale (m+2) b≤B)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M ∧ g.q≤q) :
    Tendsto (fun n => ∑' a : TotalIndex,actualMap tm i j gs m b n a) atTop
      (𝓝 (∑' a : TotalIndex,limitMap tm i j gs m b a)) :=
  tendsto_tsum_of_dominated_convergence
    (f := fun n a => actualMap tm i j gs m b n a) (g := limitMap tm i j gs m b)
    (PhysicalReactionSeries.indexMajorant_summable (2^m*(DebyeJetBounds.scale m b)^2)
      q M (width gs) B 6 (by positivity) (zero_le_one.trans hB))
    (actualMap_tendsto tm i j gs m b)
    (eventually_map_majorant tm i j gs q M b B m hq hM hb hB hbB hp)

theorem eventually_sum_eq_actual_derivative (tm : Bool) (i j : Fin 3) (gs : List Segment)
    (q M b B : ℝ) (m : ℕ) (hq : 1≤q) (hM : 0≤M) (hb : 0≤b) (hB : 1≤B)
    (hbB : degreeScale (m+2) b≤B) (hbplus : degreeScale (m+2) (b+1)≤B)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M ∧ g.q≤q) :
    ∀ᶠ n : ℕ in atTop,∀ p : Region b,
      (∑' a : TotalIndex,actualMap tm i j gs m b n a) p=
        iteratedFDeriv ℝ m (VectorReactionSeries.series tm i j (layers gs (radius n) (radius_pos n))
          (radius n) (radius n+width gs) (radius_pos n)) p.val := by
  filter_upwards [eventually_actual_summable tm i j gs q M b B m hq hM hb hB hbB hp,
    radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1*B)),
    radius_tendsto.eventually (eventually_ge_atTop (width gs))] with n hn hR ht hd
  intro p
  have heval := (ContinuousMap.evalCLM ℂ p).map_tsum hn
  have heq : (∑' a : TotalIndex,actualMap tm i j gs m b n a) p=
      ∑' a : TotalIndex,iteratedFDeriv ℝ m (term tm a i j
        (layers gs (radius n) (radius_pos n)) (radius n) (radius n+width gs) (radius_pos n)) p.val := by
    simpa only [ContinuousMap.evalCLM_apply,actualMap_apply] using heval
  rw [heq]
  have hparams := RadialScalarSeries.layers_bounds gs (radius n) (radius_pos n) q M hp
  exact (VectorReactionSeries.actual_iteratedFDeriv_series tm i j
    (layers_chain gs (radius n) (radius_pos n)) q M (width gs) B hq hM hR hB ht (by linarith) (by linarith)
    (fun g hg => ⟨(hparams g hg).1,(hparams g hg).2.1,(hparams g hg).2.2.1⟩)
    (fun g hg => (hparams g hg).2.2.2) m m le_rfl (b+1) (by linarith) hbplus p.val
    (by have h := region_norm b p; linarith)).symm

end OQ14.VectorReactionLimit
#print axioms OQ14.VectorReactionLimit.actualMap_tendsto
#print axioms OQ14.VectorReactionLimit.actualMap_apply
#print axioms OQ14.VectorReactionLimit.eventually_map_majorant
#print axioms OQ14.VectorReactionLimit.eventually_actual_summable
#print axioms OQ14.VectorReactionLimit.limiting_summable
#print axioms OQ14.VectorReactionLimit.uniform_physical_jet_limit
#print axioms OQ14.VectorReactionLimit.eventually_sum_eq_actual_derivative
