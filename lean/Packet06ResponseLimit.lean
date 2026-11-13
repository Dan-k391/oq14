import Packet06PhysicalScale
import MaterialStrongLimit
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Physical response and reciprocal-normalization convergence along varying
frequency, material and mode sequences. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ResponseLimit
open Filter MeasureTheory
open StaticCoefficient (Coefficient sqrtMultiplier)
open Packet06LocalPencil (kernel response kernel_analyticAt)
open Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem response_tendsto (c : ℕ → Coefficient) (c₀ : Coefficient) (D S T : ℝ)
    (hST : 0 ≤ T+S) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (z : ℕ → ℂ) (z₀ : ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (u : ℕ → VectorL2) (u₀ : VectorL2) (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun n => response (c n) (z n) S T (u n)) atTop (𝓝 (response c₀ z₀ S T u₀)) := by
  have hS := MaterialStrongLimit.sqrtMultiplier_varying_tendsto c c₀ D hb hb₀ ha u u₀ hu
  have hK := (kernel_analyticAt S T hST z₀).continuousAt.tendsto.comp hz
  have hev : Continuous (fun p : (VectorL2 →L[ℂ] VectorL2) × VectorL2 => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous
  exact (hev.tendsto _).comp (hK.prodMk_nhds hS)

theorem reciprocalNorm_tendsto (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (z : ℕ → ℂ) (z₀ : ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (u : ℕ → VectorL2) (u₀ : VectorL2) (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun n => reciprocalNorm (c n) R (z n) (u n)) atTop (𝓝 (reciprocalNorm c₀ R z₀ u₀)) := by
  have hS := MaterialStrongLimit.sqrtMultiplier_varying_tendsto c c₀ D hb hb₀ ha u u₀ hu
  have hK : ContinuousAt (deriv (fun w => kernel w R R)) z₀ :=
    (kernel_analyticAt R R (by positivity) z₀).deriv.continuousAt
  have hev : Continuous (fun p : (VectorL2 →L[ℂ] VectorL2) × VectorL2 => p.1 p.2) :=
    isBoundedBilinearMap_apply.continuous
  have hD := (hev.tendsto _).comp ((hK.tendsto.comp hz).prodMk_nhds hS)
  have hpair := KernelReciprocity.vectorPair_continuous.tendsto
    (deriv (fun w => kernel w R R) z₀ (sqrtMultiplier c₀ u₀),sqrtMultiplier c₀ u₀) |>.comp
      (hD.prodMk_nhds hS)
  exact (hz.div_const 2).mul hpair

theorem reciprocalNorm_eventually_nonzero (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (z : ℕ → ℂ) (z₀ : ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (u : ℕ → VectorL2) (u₀ : VectorL2) (hu : Tendsto u atTop (𝓝 u₀))
    (hN : reciprocalNorm c₀ R z₀ u₀ ≠ 0) :
    ∀ᶠ n in atTop, reciprocalNorm (c n) R (z n) (u n) ≠ 0 :=
  (reciprocalNorm_tendsto c c₀ D R hR hb hb₀ ha z z₀ hz u u₀ hu).eventually_ne hN

end OQ14.Packet06ResponseLimit
#print axioms OQ14.Packet06ResponseLimit.response_tendsto
#print axioms OQ14.Packet06ResponseLimit.reciprocalNorm_tendsto
#print axioms OQ14.Packet06ResponseLimit.reciprocalNorm_eventually_nonzero
