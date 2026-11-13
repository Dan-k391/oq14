import Packet06MaterialPencil
import Mathlib.Analysis.Complex.LocallyUniformLimit
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06MaterialHolomorphic
open Filter Set MeasureTheory Metric OQ14.StaticCoefficient OQ14.Packet06MaterialStatic
open Packet06MaterialPencil
open scoped Topology
abbrev Space := FourierL2.Space

theorem compactPart_differentiable (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) :
    Differentiable ℂ (fun z => compactPart c z R) := by
  unfold compactPart
  exact ((differentiable_const (Ring.inverse (staticBlock c))).mul
    (ComplexConvolutionAnalytic.operator_differentiable (2*R) (by positivity))).mul
      (differentiable_const (materialMultiplier c))

theorem compactPart_locally_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0) :
    TendstoLocallyUniformlyOn (fun n z => compactPart (c n) z R)
      (fun z => compactPart c₀ z R) atTop univ := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
  intro A _ hA
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have h := compactPart_uniform c c₀ D R hR hb hb₀ ha hc hc₀ A hA ε hε
  filter_upwards [h] with n hn z hz
  simpa only [dist_eq_norm, norm_sub_rev] using hn z hz
#print axioms OQ14.Packet06MaterialHolomorphic.compactPart_differentiable
#print axioms OQ14.Packet06MaterialHolomorphic.compactPart_locally_uniform
end OQ14.Packet06MaterialHolomorphic
