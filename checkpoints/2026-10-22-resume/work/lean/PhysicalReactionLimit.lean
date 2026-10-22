import PhysicalReactionSeries
import RadialScalarSeries
import Mathlib.Topology.ContinuousMap.Compact

/-! Actual compact spatial jet limits for the physical finite-stack mode series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.PhysicalReactionLimit
open Filter Set Metric Complex OQ14.Maxwell OQ14.RadialStack OQ14.RadialFiniteLimit
  OQ14.RadialPhaseLimit OQ14.SphereHarmonicHilbert OQ14.SpatialReactionTerms
  OQ14.HarmonicSpatialMajorant
open scoped Topology

abbrev Region (b : ℝ) := ↥(closedBall (0 : Space × Space) b)
abbrev Jet (j : ℕ) := ContinuousMultilinearMap ℝ (fun _ : Fin j => Space × Space) ℂ

instance region_compact (b : ℝ) : CompactSpace (Region b) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Space × Space) b)

theorem region_norm (b : ℝ) (p : Region b) : ‖p.val‖ ≤ b := mem_closedBall_zero_iff.mp p.property

def basisJetMap (a : TotalIndex) (j : ℕ) (b : ℝ) : C(Region b,Jet j) where
  toFun p := iteratedFDeriv ℝ j (basisProduct a 1 1) p.val
  continuous_toFun := ((basisProduct_smooth a 1 1).continuous_iteratedFDeriv
    (by exact_mod_cast le_top)).comp continuous_subtype_val

def actualMap (gs : List Segment) (j : ℕ) (b : ℝ) (n : ℕ) (a : TotalIndex) : C(Region b,Jet j) :=
  (-(RadialSource.gamma a.1 (layers gs (radius n) (radius_pos n))
    (radius n) (radius n+width gs) (radius_pos n)+I)) • basisJetMap a j b

def limitMap (gs : List Segment) (j : ℕ) (b : ℝ) (a : TotalIndex) : C(Region b,Jet j) :=
  (-((limitingCoefficients a.1 gs).1/(limitingCoefficients a.1 gs).2+I)) • basisJetMap a j b

theorem actualMap_tendsto (gs : List Segment) (j : ℕ) (b : ℝ) (a : TotalIndex) :
    Tendsto (fun n => actualMap gs j b n a) atTop (𝓝 (limitMap gs j b a)) :=
  ((actual_gamma_limit a.1 gs).add_const I).neg.smul_const (basisJetMap a j b)

theorem actualMap_apply (gs : List Segment) (j : ℕ) (b : ℝ) (n : ℕ) (a : TotalIndex) (p : Region b) :
    actualMap gs j b n a p=
      iteratedFDeriv ℝ j (PhysicalScalarReaction.term a (layers gs (radius n) (radius_pos n))
        (radius n) (radius n+width gs) (radius_pos n)) p.val := by
  have hf : ContDiffAt ℝ (j : ℕ∞) (basisProduct a 1 1) p.val :=
    (basisProduct_smooth a 1 1).contDiffAt.of_le (by exact_mod_cast le_top)
  exact (iteratedFDeriv_const_smul_apply
    (a := -(RadialSource.gamma a.1 (layers gs (radius n) (radius_pos n))
      (radius n) (radius n+width gs) (radius_pos n)+I)) hf).symm

theorem eventually_map_majorant (gs : List Segment) (q M b B : ℝ) (j : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 ≤ b) (hB : 1 ≤ B) (hbB : degreeScale j b ≤ B)
    (hp : ∀ g∈gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    ∀ᶠ n : ℕ in atTop,∀ a : TotalIndex,
      ‖actualMap gs j b n a‖ ≤
        PhysicalReactionSeries.indexMajorant (2^j*(lowerJetScale 1 j b)^2) q M (width gs) B 6 a := by
  filter_upwards [radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1*B)),
    radius_tendsto.eventually (eventually_ge_atTop (width gs))] with n hR ht hd
  intro a
  have hrad := RadialFullMajorant.majorant_nonnegative q M (width gs) B 6 a.1
  have hfree := RadialFullMajorant.majorant_nonnegative 1 0 0 B 6 a.1
  have hbound : 0 ≤ PhysicalReactionSeries.indexMajorant (2^j*(lowerJetScale 1 j b)^2)
      q M (width gs) B 6 a := by
    dsimp [PhysicalReactionSeries.indexMajorant,PhysicalReactionSeries.radialMajorant]
    positivity
  rw [(actualMap gs j b n a).norm_le hbound]
  intro p
  rw [actualMap_apply]
  have hparams := RadialScalarSeries.layers_bounds gs (radius n) (radius_pos n) q M hp
  exact PhysicalReactionSeries.actual_joint_jet_bound a (layers_chain gs (radius n) (radius_pos n))
    q M (width gs) B hq hM hR hB ht (by linarith) (by linarith)
    (fun g hg => ⟨(hparams g hg).1,(hparams g hg).2.1,(hparams g hg).2.2.1⟩)
    (fun g hg => (hparams g hg).2.2.2) j j le_rfl b hb hbB p.val (region_norm b p)

theorem eventually_actual_summable (gs : List Segment) (q M b B : ℝ) (j : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 ≤ b) (hB : 1 ≤ B) (hbB : degreeScale j b ≤ B)
    (hp : ∀ g∈gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    ∀ᶠ n : ℕ in atTop,Summable (actualMap gs j b n) := by
  filter_upwards [eventually_map_majorant gs q M b B j hq hM hb hB hbB hp] with n hn
  exact Summable.of_norm_bounded (f := actualMap gs j b n) _
    (PhysicalReactionSeries.indexMajorant_summable (2^j*(lowerJetScale 1 j b)^2) q M (width gs) B 6 (by positivity) (zero_le_one.trans hB)) hn

theorem limiting_summable (gs : List Segment) (q M b B : ℝ) (j : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 ≤ b) (hB : 1 ≤ B) (hbB : degreeScale j b ≤ B)
    (hp : ∀ g∈gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    Summable (limitMap gs j b) := by
  apply Summable.of_norm_bounded (f := limitMap gs j b) _
    (PhysicalReactionSeries.indexMajorant_summable (2^j*(lowerJetScale 1 j b)^2) q M (width gs) B 6 (by positivity) (zero_le_one.trans hB))
  intro a
  have hnlim : Tendsto (fun n => ‖actualMap gs j b n a‖) atTop (𝓝 ‖limitMap gs j b a‖) :=
    (continuous_norm.tendsto (limitMap gs j b a)).comp (actualMap_tendsto gs j b a)
  apply le_of_tendsto hnlim
  filter_upwards [eventually_map_majorant gs q M b B j hq hM hb hB hbB hp] with n hn
  exact hn a

theorem uniform_physical_jet_limit (gs : List Segment) (q M b B : ℝ) (j : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 ≤ b) (hB : 1 ≤ B) (hbB : degreeScale j b ≤ B)
    (hp : ∀ g∈gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    Tendsto (fun n => ∑' a : TotalIndex,actualMap gs j b n a) atTop
      (𝓝 (∑' a : TotalIndex,limitMap gs j b a)) :=
  tendsto_tsum_of_dominated_convergence (f := fun n a => actualMap gs j b n a) (g := limitMap gs j b)
    (PhysicalReactionSeries.indexMajorant_summable (2^j*(lowerJetScale 1 j b)^2) q M (width gs) B 6 (by positivity) (zero_le_one.trans hB))
    (actualMap_tendsto gs j b)
    (eventually_map_majorant gs q M b B j hq hM hb hB hbB hp)


theorem eventually_sum_eq_actual_derivative (gs : List Segment) (q M b B : ℝ) (j : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 ≤ b) (hB : 1 ≤ B)
    (hbB : degreeScale j b ≤ B) (hbplus : degreeScale j (b+1) ≤ B)
    (hp : ∀ g∈gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    ∀ᶠ n : ℕ in atTop,∀ p : Region b,
      (∑' a : TotalIndex,actualMap gs j b n a) p=
        iteratedFDeriv ℝ j (PhysicalReactionSeries.series (layers gs (radius n) (radius_pos n))
          (radius n) (radius n+width gs) (radius_pos n)) p.val := by
  filter_upwards [eventually_actual_summable gs q M b B j hq hM hb hB hbB hp,
    radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1*B)),
    radius_tendsto.eventually (eventually_ge_atTop (width gs))] with n hn hR ht hd
  intro p
  have heval := (ContinuousMap.evalCLM ℂ p).map_tsum hn
  have heq : (∑' a : TotalIndex,actualMap gs j b n a) p=
      ∑' a : TotalIndex,iteratedFDeriv ℝ j (PhysicalScalarReaction.term a
        (layers gs (radius n) (radius_pos n)) (radius n) (radius n+width gs) (radius_pos n)) p.val := by
    simpa only [ContinuousMap.evalCLM_apply,actualMap_apply] using heval
  rw [heq]
  have hparams := RadialScalarSeries.layers_bounds gs (radius n) (radius_pos n) q M hp
  exact (PhysicalReactionSeries.actual_iteratedFDeriv_series (layers_chain gs (radius n) (radius_pos n))
    q M (width gs) B hq hM hR hB ht (by linarith) (by linarith)
    (fun g hg => ⟨(hparams g hg).1,(hparams g hg).2.1,(hparams g hg).2.2.1⟩)
    (fun g hg => (hparams g hg).2.2.2) j j le_rfl (b+1) (by linarith) hbplus p.val
    (by have hh := region_norm b p;linarith)).symm

end OQ14.PhysicalReactionLimit

#print axioms OQ14.PhysicalReactionLimit.region_compact

#print axioms OQ14.PhysicalReactionLimit.region_norm

#print axioms OQ14.PhysicalReactionLimit.actualMap_tendsto

#print axioms OQ14.PhysicalReactionLimit.actualMap_apply

#print axioms OQ14.PhysicalReactionLimit.eventually_map_majorant

#print axioms OQ14.PhysicalReactionLimit.eventually_actual_summable

#print axioms OQ14.PhysicalReactionLimit.limiting_summable

#print axioms OQ14.PhysicalReactionLimit.uniform_physical_jet_limit

#print axioms OQ14.PhysicalReactionLimit.eventually_sum_eq_actual_derivative
