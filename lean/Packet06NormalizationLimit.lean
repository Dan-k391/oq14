import Packet06ResponseLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Compatible local square-root normalization along a convergent mode branch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06NormalizationLimit
open Filter Complex
open scoped Topology

theorem compatible_scales (N : ℕ → ℂ) (N₀ a₀ : ℂ)
    (hN : Tendsto N atTop (𝓝 N₀)) (hN₀ : N₀ ≠ 0) (ha₀ : a₀^2*N₀ = 1) :
    ∃ a : ℕ → ℂ, Tendsto a atTop (𝓝 a₀) ∧
      (∀ j, a j ≠ 0) ∧ (∀ᶠ j in atTop, (a j)^2*N j = 1) := by
  have ha : a₀ ≠ 0 := by intro h; rw [h,zero_pow (by decide : 2 ≠ 0),zero_mul] at ha₀; exact zero_ne_one ha₀
  let a : ℕ → ℂ := fun j => a₀*exp (log (N₀/N j)/2)
  have hratio : Tendsto (fun j => N₀/N j) atTop (𝓝 (1 : ℂ)) := by
    simpa only [div_self hN₀] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => N₀) atTop (𝓝 N₀)).div hN hN₀
  have hlog : Tendsto (fun j => log (N₀/N j)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [log_one] using hratio.clog one_mem_slitPlane
  have hhalf : Tendsto (fun j => log (N₀/N j)/2) atTop (𝓝 (0 : ℂ)) := by
    simpa only [zero_div] using hlog.div_const 2
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : ℕ => a₀) atTop (𝓝 a₀)).mul
    ((continuous_exp.tendsto (0 : ℂ)).comp hhalf)
  refine ⟨a,?_,fun j => mul_ne_zero ha (exp_ne_zero _),?_⟩
  · simpa only [zero_div,exp_zero,mul_one] using hlim
  · filter_upwards [hN.eventually_ne hN₀] with j hj
    have hsq : exp (log (N₀/N j)/2)^2 = N₀/N j := by
      rw [pow_two,←exp_add,show log (N₀/N j)/2+log (N₀/N j)/2=log (N₀/N j) by ring,
        exp_log (div_ne_zero hN₀ hj)]
    change (a₀*exp (log (N₀/N j)/2))^2*N j = 1
    rw [mul_pow,hsq,mul_assoc,div_mul_cancel₀ _ hj]
    exact ha₀

theorem compatible_mode_scales (c : ℕ → StaticCoefficient.Coefficient)
    (R : ℝ) (hR : 0 ≤ R) (z : ℕ → ℂ) (u : ℕ → VectorFourier.VectorL2)
    (u₀ : VectorFourier.VectorL2) (N₀ a₀ : ℂ)
    (hu : Tendsto u atTop (𝓝 u₀))
    (hN : Tendsto (fun j => Packet06PhysicalNormalization.reciprocalNorm (c j) R (z j) (u j)) atTop (𝓝 N₀))
    (hN₀ : N₀ ≠ 0) (ha₀ : a₀^2*N₀ = 1) :
    ∃ a : ℕ → ℂ, Tendsto (fun j => a j • u j) atTop (𝓝 (a₀ • u₀)) ∧
      (∀ j, a j ≠ 0) ∧ (∀ᶠ j in atTop,
        Packet06PhysicalNormalization.reciprocalNorm (c j) R (z j) (a j • u j) = 1) := by
  obtain ⟨a,ha,hane,hunit⟩ := compatible_scales _ N₀ a₀ hN hN₀ ha₀
  refine ⟨a,ha.smul hu,hane,?_⟩
  filter_upwards [hunit] with j hj
  rw [Packet06PhysicalScale.reciprocalNorm_scale _ R hR]
  exact hj

end OQ14.Packet06NormalizationLimit
#print axioms OQ14.Packet06NormalizationLimit.compatible_scales
#print axioms OQ14.Packet06NormalizationLimit.compatible_mode_scales
