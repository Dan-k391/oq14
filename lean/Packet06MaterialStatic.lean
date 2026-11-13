import Packet06WeightedTransport
import MaterialStrongLimit
import StaticNewton

/-! Strong bounded-a.e. material convergence for the actual unweighted
static electric pencil. This does not assert multiplier-norm convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
namespace OQ14.Packet06MaterialStatic
open MeasureTheory Filter OQ14.StaticCoefficient OQ14.MaterialStrongLimit
open scoped Topology

abbrev VectorL2 := VectorFourier.VectorL2

def materialMultiplier (c : Coefficient) : VectorL2 →L[ℂ] VectorL2 :=
  sqrtMultiplier c * sqrtMultiplier c

def staticBlock (c : Coefficient) : VectorL2 →L[ℂ] VectorL2 :=
  1 + VectorFourier.physicalProjection * materialMultiplier c

theorem materialMultiplier_ae (c : Coefficient) (f : VectorL2) :
    materialMultiplier c f =ᵐ[volume] fun x => (c.value x : ℂ) • f x :=
  sqrtMultiplier_square_ae c f

theorem materialMultiplier_strong (c : ℕ → Coefficient) (c₀ : Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (f : VectorL2) : Tendsto (fun n => materialMultiplier (c n) f) atTop (𝓝 (materialMultiplier c₀ f)) := by
  exact sqrtMultiplier_varying_tendsto c c₀ D hb hb₀ ha _ _
    (sqrtMultiplier_tendsto c c₀ D hb hb₀ ha f)

theorem materialMultiplier_norm_le (c : Coefficient) : ‖materialMultiplier c‖ ≤ c.bound := by
  have h := norm_mul_le (sqrtMultiplier c) (sqrtMultiplier c)
  have hs := sqrtMultiplier_norm_le c
  have hsq : Real.sqrt c.bound * Real.sqrt c.bound = c.bound := Real.mul_self_sqrt (bound_nonnegative c)
  calc
    ‖materialMultiplier c‖ ≤ ‖sqrtMultiplier c‖ * ‖sqrtMultiplier c‖ := h
    _ ≤ Real.sqrt c.bound * Real.sqrt c.bound := mul_self_le_mul_self (norm_nonneg _) hs
    _ = c.bound := hsq

theorem staticBlock_isUnit (c : Coefficient) : IsUnit (staticBlock c) := by
  have h := Packet06WeightedTransport.weighted_inverse_formula (sqrtMultiplier c)
    (-VectorFourier.physicalProjection) (by
      simpa only [StaticCoefficient.weightedBlock, StaticNewton.volumeBlock_eq,
        mul_neg, neg_mul, sub_neg_eq_add] using StaticCoefficient.weightedBlock_isUnit c)
  simpa only [staticBlock, materialMultiplier, neg_mul, sub_neg_eq_add] using h.1

theorem staticBlock_inverse_norm_le (c : Coefficient) :
    ‖Ring.inverse (staticBlock c)‖ ≤ 1+c.bound := by
  have hw : 1-sqrtMultiplier c*(-VectorFourier.physicalProjection)*sqrtMultiplier c =
      StaticCoefficient.weightedBlock c := by
    simp only [StaticCoefficient.weightedBlock]
    noncomm_ring
  have hb : 1-(-VectorFourier.physicalProjection)*sqrtMultiplier c*sqrtMultiplier c =
      staticBlock c := by
    simp only [staticBlock, materialMultiplier]
    noncomm_ring
  have h := Packet06WeightedTransport.weighted_inverse_formula (sqrtMultiplier c)
    (-VectorFourier.physicalProjection) (hw.symm ▸ StaticCoefficient.weightedBlock_isUnit c)
  rw [hb, hw] at h
  have he : Ring.inverse (staticBlock c) =
      1 - VectorFourier.physicalProjection * sqrtMultiplier c *
        Ring.inverse (StaticCoefficient.weightedBlock c) * sqrtMultiplier c := by
    rw [h.2]
    noncomm_ring
  rw [he]
  have hs := sqrtMultiplier_norm_le c
  have hp := VectorFourier.physicalProjection_norm_le
  have hi := StaticCoefficient.weightedBlock_inverse_norm_le c
  have hsq : Real.sqrt c.bound * Real.sqrt c.bound = c.bound := Real.mul_self_sqrt (bound_nonnegative c)
  have hone : ‖(1 : VectorL2 →L[ℂ] VectorL2)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simp
  have h1 : ‖VectorFourier.physicalProjection‖ * ‖sqrtMultiplier c‖ ≤ Real.sqrt c.bound := by
    calc
      _ ≤ 1 * ‖sqrtMultiplier c‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ Real.sqrt c.bound := by simpa using hs
  have h2 : ‖VectorFourier.physicalProjection‖ * ‖sqrtMultiplier c‖ *
      ‖Ring.inverse (StaticCoefficient.weightedBlock c)‖ ≤ Real.sqrt c.bound := by
    calc
      _ ≤ (‖VectorFourier.physicalProjection‖ * ‖sqrtMultiplier c‖) * 1 :=
        mul_le_mul_of_nonneg_left hi (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ ≤ Real.sqrt c.bound := by simpa using h1
  calc
    ‖1 - VectorFourier.physicalProjection * sqrtMultiplier c *
      Ring.inverse (StaticCoefficient.weightedBlock c) * sqrtMultiplier c‖ ≤
      ‖(1 : VectorL2 →L[ℂ] VectorL2)‖ +
        ‖VectorFourier.physicalProjection * sqrtMultiplier c * Ring.inverse (StaticCoefficient.weightedBlock c) * sqrtMultiplier c‖ := norm_sub_le _ _
    _ ≤ 1 + (‖VectorFourier.physicalProjection‖ * ‖sqrtMultiplier c‖ *
          ‖Ring.inverse (StaticCoefficient.weightedBlock c)‖ * ‖sqrtMultiplier c‖) := by
      apply add_le_add hone
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ 1 + Real.sqrt c.bound * Real.sqrt c.bound := by
      apply add_le_add_left
      exact mul_le_mul h2 hs (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = 1+c.bound := by rw [hsq]

theorem staticBlock_strong (c : ℕ → Coefficient) (c₀ : Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (f : VectorL2) : Tendsto (fun n => staticBlock (c n) f) atTop (𝓝 (staticBlock c₀ f)) := by
  have hm := materialMultiplier_strong c c₀ D hb hb₀ ha f
  exact tendsto_const_nhds.add (VectorFourier.physicalProjection.continuous.tendsto _ |>.comp hm)

/-- Static inverses converge strongly under uniform bounded a.e. rounding. -/
theorem staticBlock_inverse_strong (c : ℕ → Coefficient) (c₀ : Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (f : VectorL2) : Tendsto (fun n => Ring.inverse (staticBlock (c n)) f) atTop
      (𝓝 (Ring.inverse (staticBlock c₀) f)) := by
  let u := Ring.inverse (staticBlock c₀) f
  have hAu : staticBlock c₀ u = f := by
    have h := congrArg (fun A : VectorL2 →L[ℂ] VectorL2 => A f)
      (Ring.mul_inverse_cancel (staticBlock c₀) (staticBlock_isUnit c₀))
    exact h
  have hres : Tendsto (fun n => f - staticBlock (c n) u) atTop (𝓝 0) := by
    have hf : Tendsto (fun _ : ℕ => f) atTop (𝓝 f) := tendsto_const_nhds
    simpa only [hAu, sub_self] using hf.sub (staticBlock_strong c c₀ D hb hb₀ ha u)
  have hbound (n : ℕ) : ‖Ring.inverse (staticBlock (c n)) f - u‖ ≤
      (1+D)*‖f-staticBlock (c n) u‖ := by
    have hcancel : Ring.inverse (staticBlock (c n)) (staticBlock (c n) u) = u := by
      have h := congrArg (fun A : VectorL2 →L[ℂ] VectorL2 => A u)
        (Ring.inverse_mul_cancel (staticBlock (c n)) (staticBlock_isUnit (c n)))
      exact h
    have heq : Ring.inverse (staticBlock (c n)) f - u =
        Ring.inverse (staticBlock (c n)) (f - staticBlock (c n) u) := by
      rw [map_sub, hcancel]
    rw [heq]
    exact ((Ring.inverse (staticBlock (c n))).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right ((staticBlock_inverse_norm_le (c n)).trans (by linarith [hb n])) (norm_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh : Tendsto (fun n => (1+D)*‖f-staticBlock (c n) u‖) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hres.norm
  exact squeeze_zero (fun n => norm_nonneg _) hbound hh

#print axioms OQ14.Packet06MaterialStatic.materialMultiplier_ae
#print axioms OQ14.Packet06MaterialStatic.materialMultiplier_strong
#print axioms OQ14.Packet06MaterialStatic.materialMultiplier_norm_le
#print axioms OQ14.Packet06MaterialStatic.staticBlock_isUnit
#print axioms OQ14.Packet06MaterialStatic.staticBlock_inverse_norm_le
#print axioms OQ14.Packet06MaterialStatic.staticBlock_strong
#print axioms OQ14.Packet06MaterialStatic.staticBlock_inverse_strong
end OQ14.Packet06MaterialStatic
