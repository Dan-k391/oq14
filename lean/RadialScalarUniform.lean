import RadialScalarSeries
import Mathlib.Topology.ContinuousMap.Compact

/-! Uniform compact all-order scalar reaction series limits in an actual sup-norm space. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialScalarUniform

open Filter Set Metric Complex OQ14.RadialStack OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit
open OQ14.RiccatiOriginSeries OQ14.RiccatiCompactDerivatives
open scoped Topology

abbrev Region (s : ℝ) := ↥((closedBall (0 : ℂ) s) ×ˢ (closedBall (0 : ℂ) s))

instance region_compact (s : ℝ) : CompactSpace (Region s) :=
  isCompact_iff_compactSpace.mp
    ((isCompact_closedBall (0 : ℂ) s).prod (isCompact_closedBall (0 : ℂ) s))

theorem left_norm (s : ℝ) (p : Region s) : ‖p.val.1‖ ≤ s := by
  simpa only [mem_closedBall,dist_zero_right] using p.property.1

theorem right_norm (s : ℝ) (p : Region s) : ‖p.val.2‖ ≤ s := by
  simpa only [mem_closedBall,dist_zero_right] using p.property.2

def basisMap (l m n : ℕ) (s : ℝ) : C(Region s,ℂ) where
  toFun p := iteratedDeriv m (origin l) p.val.1*iteratedDeriv n (origin l) p.val.2
  continuous_toFun := by
    have hm := ((entire_origin l).differentiable_iteratedDeriv m (by exact_mod_cast ENat.coe_lt_top m)).continuous
    have hn := ((entire_origin l).differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)).continuous
    exact (hm.comp (continuous_fst.comp continuous_subtype_val)).mul
      (hn.comp (continuous_snd.comp continuous_subtype_val))

def actualMap (gs : List Segment) (k m n : ℕ) (s : ℝ) (j l : ℕ) : C(Region s,ℂ) :=
  ((l+1 : ℝ)^k) • (RadialSource.gamma l (layers gs (radius j) (radius_pos j))
    (radius j) (radius j+width gs) (radius_pos j) • basisMap l m n s)

def limitMap (gs : List Segment) (k m n : ℕ) (s : ℝ) (l : ℕ) : C(Region s,ℂ) :=
  ((l+1 : ℝ)^k) • (((limitingCoefficients l gs).1/(limitingCoefficients l gs).2) • basisMap l m n s)

theorem actualMap_apply (gs : List Segment) (k m n : ℕ) (s : ℝ) (j l : ℕ) (p : Region s) :
    actualMap gs k m n s j l p = RadialScalarSeries.actualTerm gs k m n p.val.1 p.val.2 j l := by
  simp only [actualMap,ContinuousMap.smul_apply,basisMap,ContinuousMap.coe_mk,smul_eq_mul,
    RadialScalarSeries.actualTerm,RadialEntireReaction.component,mul_assoc]

theorem limitMap_apply (gs : List Segment) (k m n : ℕ) (s : ℝ) (l : ℕ) (p : Region s) :
    limitMap gs k m n s l p = RadialScalarSeries.limitTerm gs k m n p.val.1 p.val.2 l := by
  simp only [limitMap,ContinuousMap.smul_apply,basisMap,ContinuousMap.coe_mk,smul_eq_mul,
    RadialScalarSeries.limitTerm,mul_assoc]

theorem actualMap_tendsto (gs : List Segment) (k m n : ℕ) (s : ℝ) (l : ℕ) :
    Tendsto (fun j : ℕ => actualMap gs k m n s j l) atTop (𝓝 (limitMap gs k m n s l)) :=
  ((actual_gamma_limit l gs).smul_const (basisMap l m n s)).const_smul ((l+1 : ℝ)^k)

theorem eventually_map_majorant (gs : List Segment) (q M s b : ℝ) (k m n : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 < b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    ∀ᶠ j : ℕ in atTop, ∀ l : ℕ,
      ‖actualMap gs k m n s j l‖ ≤ RadialFullMajorant.majorant q M (width gs) b k l := by
  filter_upwards [radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1*b)),
    radius_tendsto.eventually (eventually_ge_atTop (width gs))] with j hR ht hd
  intro l
  rw [(actualMap gs k m n s j l).norm_le (RadialFullMajorant.majorant_nonnegative q M (width gs) b k l)]
  intro p
  rw [actualMap_apply]
  have hparams := RadialScalarSeries.layers_bounds gs (radius j) (radius_pos j) q M hp
  have h := RadialFullMajorant.component_weighted_bound l k m n
    (layers_chain gs (radius j) (radius_pos j)) q M (width gs) b hq hM hR hb ht
    (by linarith) (by linarith)
    (fun g hg => ⟨(hparams g hg).1,(hparams g hg).2.1,(hparams g hg).2.2.1⟩)
    (fun g hg => (hparams g hg).2.2.2) p.val.1 p.val.2
    (by linarith [left_norm s p]) (by linarith [right_norm s p])
  simpa only [RadialScalarSeries.actualTerm,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (l+1 : ℝ)^k)] using h

theorem eventually_actual_summable (gs : List Segment) (q M s b : ℝ) (k m n : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 < b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    ∀ᶠ j : ℕ in atTop, Summable (actualMap gs k m n s j) := by
  filter_upwards [eventually_map_majorant gs q M s b k m n hq hM hb hmb hnb hp] with j hj
  exact Summable.of_norm_bounded _ (RadialFullMajorant.majorant_summable q M (width gs) b k hb.le) hj

theorem limiting_summable (gs : List Segment) (q M s b : ℝ) (k m n : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 < b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    Summable (limitMap gs k m n s) := by
  apply Summable.of_norm_bounded _ (RadialFullMajorant.majorant_summable q M (width gs) b k hb.le)
  intro l
  apply le_of_tendsto (actualMap_tendsto gs k m n s l).norm
  filter_upwards [eventually_map_majorant gs q M s b k m n hq hM hb hmb hnb hp] with j hj
  exact hj l

theorem uniform_actual_series_limit (gs : List Segment) (q M s b : ℝ) (k m n : ℕ)
    (hq : 1 ≤ q) (hM : 0 ≤ M) (hb : 0 < b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M ∧ g.q ≤ q) :
    Tendsto (fun j : ℕ => ∑' l : ℕ, actualMap gs k m n s j l) atTop
      (𝓝 (∑' l : ℕ, limitMap gs k m n s l)) := by
  exact tendsto_tsum_of_dominated_convergence
    (RadialFullMajorant.majorant_summable q M (width gs) b k hb.le)
    (actualMap_tendsto gs k m n s)
    (eventually_map_majorant gs q M s b k m n hq hM hb hmb hnb hp)

end OQ14.RadialScalarUniform

#print axioms OQ14.RadialScalarUniform.region_compact
#print axioms OQ14.RadialScalarUniform.left_norm
#print axioms OQ14.RadialScalarUniform.right_norm
#print axioms OQ14.RadialScalarUniform.actualMap_apply
#print axioms OQ14.RadialScalarUniform.limitMap_apply
#print axioms OQ14.RadialScalarUniform.actualMap_tendsto
#print axioms OQ14.RadialScalarUniform.eventually_map_majorant
#print axioms OQ14.RadialScalarUniform.eventually_actual_summable
#print axioms OQ14.RadialScalarUniform.limiting_summable
#print axioms OQ14.RadialScalarUniform.uniform_actual_series_limit
