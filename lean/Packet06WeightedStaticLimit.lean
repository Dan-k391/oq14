import Packet06MaterialStatic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06WeightedStaticLimit
open Filter MeasureTheory OQ14.StaticCoefficient OQ14.MaterialStrongLimit
open scoped Topology
abbrev V := VectorFourier.VectorL2

theorem weightedBlock_strong (c : ℕ → Coefficient) (c₀ : Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x))) (f : V) :
    Tendsto (fun n => weightedBlock (c n) f) atTop (𝓝 (weightedBlock c₀ f)) := by
  have hS := sqrtMultiplier_tendsto c c₀ D hb hb₀ ha f
  have hP := VectorFourier.physicalProjection.continuous.tendsto _ |>.comp hS
  have hv := sqrtMultiplier_varying_tendsto c c₀ D hb hb₀ ha _ _ hP
  exact tendsto_const_nhds.add hv

theorem weightedBlock_inverse_strong (c : ℕ → Coefficient) (c₀ : Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x))) (f : V) :
    Tendsto (fun n => Ring.inverse (weightedBlock (c n)) f) atTop
      (𝓝 (Ring.inverse (weightedBlock c₀) f)) := by
  let u := Ring.inverse (weightedBlock c₀) f
  have hAu : weightedBlock c₀ u = f := by
    exact congrArg (fun A : V →L[ℂ] V => A f)
      (Ring.mul_inverse_cancel (weightedBlock c₀) (weightedBlock_isUnit c₀))
  have hres : Tendsto (fun n => f - weightedBlock (c n) u) atTop (𝓝 0) := by
    have hf : Tendsto (fun _ : ℕ => f) atTop (𝓝 f) := tendsto_const_nhds
    simpa only [hAu,sub_self] using hf.sub (weightedBlock_strong c c₀ D hb hb₀ ha u)
  have hbound (n : ℕ) : ‖Ring.inverse (weightedBlock (c n)) f - u‖ ≤
      ‖f-weightedBlock (c n) u‖ := by
    have hcancel : Ring.inverse (weightedBlock (c n)) (weightedBlock (c n) u) = u := by
      exact congrArg (fun A : V →L[ℂ] V => A u)
        (Ring.inverse_mul_cancel (weightedBlock (c n)) (weightedBlock_isUnit (c n)))
    have heq : Ring.inverse (weightedBlock (c n)) f - u =
        Ring.inverse (weightedBlock (c n)) (f-weightedBlock (c n) u) := by rw [map_sub,hcancel]
    rw [heq]
    exact ((Ring.inverse (weightedBlock (c n))).le_opNorm _).trans (by
      simpa using mul_le_mul_of_nonneg_right (weightedBlock_inverse_norm_le (c n)) (norm_nonneg _))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hbound (by simpa using hres.norm)
#print axioms OQ14.Packet06WeightedStaticLimit.weightedBlock_strong
#print axioms OQ14.Packet06WeightedStaticLimit.weightedBlock_inverse_strong
end OQ14.Packet06WeightedStaticLimit
