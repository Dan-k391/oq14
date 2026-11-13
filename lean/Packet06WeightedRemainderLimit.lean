import Packet06WeightedStaticLimit
import Packet06MaterialDynamic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06WeightedRemainderLimit
open Filter Set MeasureTheory Metric OQ14.StaticCoefficient OQ14.MaterialStrongLimit
open scoped Topology InnerProduct
abbrev V := VectorFourier.VectorL2
abbrev Space := FourierL2.Space

theorem weightedRemainder_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0)
    (A : Set ℂ) (hA : IsCompact A) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ A,
      ‖ComplexConvolutionAnalytic.weightedRemainder (c n) z R -
        ComplexConvolutionAnalytic.weightedRemainder c₀ z R‖ < ε := by
  let T : ℕ → V →L[ℂ] V := fun n => sqrtMultiplier (c n) - sqrtMultiplier c₀
  let Q := sqrtMultiplier (RestrictedTEParitySandwich.ballCoefficient R)
  let K : ℂ → V →L[ℂ] V := fun z => ComplexConvolutionAnalytic.operator z (2*R) * Q
  let L : ℂ → V →L[ℂ] V := fun z => ComplexConvolutionAnalytic.operator z (2*R) * sqrtMultiplier c₀
  have hD : 0 ≤ D := (bound_nonnegative c₀).trans hb₀
  have hbound (n : ℕ) : ‖T n‖ ≤ 2*Real.sqrt D := by
    have h1 := (sqrtMultiplier_norm_le (c n)).trans (Real.sqrt_le_sqrt (hb n))
    have h2 := (sqrtMultiplier_norm_le c₀).trans (Real.sqrt_le_sqrt hb₀)
    exact (norm_sub_le _ _).trans (by linarith)
  have hstrong (f : V) : Tendsto (fun n => T n f) atTop (𝓝 0) := by
    change Tendsto (fun n => sqrtMultiplier (c n) f - sqrtMultiplier c₀ f) atTop (𝓝 0)
    simpa using (sqrtMultiplier_tendsto c c₀ D hb hb₀ ha f).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => sqrtMultiplier c₀ f) atTop (𝓝 (sqrtMultiplier c₀ f)))
  have hadj (n : ℕ) : (T n)† = T n := by
    simp only [T, map_sub, (sqrtMultiplier_selfAdjoint _).adjoint_eq]
  have hstrong' (f : V) : Tendsto (fun n => ((T n)†) f) atTop (𝓝 0) := by
    simpa only [hadj] using hstrong f
  have hcontK : ContinuousOn K A := by
    exact (((ComplexConvolutionAnalytic.operator_differentiable (2*R) (by positivity)).mul
      (differentiable_const Q)).continuous).continuousOn
  have hcontL : ContinuousOn L A := by
    exact (((ComplexConvolutionAnalytic.operator_differentiable (2*R) (by positivity)).mul
      (differentiable_const (sqrtMultiplier c₀))).continuous).continuousOn
  have hcompactK (z : ℂ) : IsCompactOperator (K z) := by
    apply ComplexConvolutionAnalytic.source_operator_compact (RestrictedTEParitySandwich.ballCoefficient R) z R
    intro x hx
    rw [RestrictedTEParitySandwich.ballCoefficient_value]
    simp [hx]
  have hcompactL (z : ℂ) : IsCompactOperator (L z) :=
    ComplexConvolutionAnalytic.source_operator_compact c₀ z R hc₀
  have hleft := Packet06CompactAdjoint.compact_left_family_uniform T (2*Real.sqrt D) (by positivity)
    hbound hstrong' K A hA hcontK (fun z _ => hcompactK z)
  have hright := Packet06StrongCompact.compact_family_uniform T (2*Real.sqrt D) (by positivity)
    hbound hstrong L A hA hcontL (fun z _ => hcompactL z)
  have hQ (n : ℕ) : Q * T n = T n := by
    dsimp [Q,T]
    rw [mul_sub,Packet06MaterialDynamic.ball_cut_sqrt (c n) R (hc n),
      Packet06MaterialDynamic.ball_cut_sqrt c₀ R hc₀]
  intro ε hε
  have hδ : 0 < ε/(2*(Real.sqrt D+1)) := by positivity
  filter_upwards [hleft (ε/(2*(Real.sqrt D+1))) hδ, hright (ε/2) (by positivity)] with n hnL hnR z hz
  have h1 := hnL z hz
  have h2 := hnR z hz
  have hS : ‖sqrtMultiplier (c n)‖ ≤ Real.sqrt D :=
    (sqrtMultiplier_norm_le (c n)).trans (Real.sqrt_le_sqrt (hb n))
  have he : ComplexConvolutionAnalytic.weightedRemainder (c n) z R -
      ComplexConvolutionAnalytic.weightedRemainder c₀ z R =
      T n * L z + sqrtMultiplier (c n) * (K z * T n) := by
    dsimp [ComplexConvolutionAnalytic.weightedRemainder,L,K]
    change sqrtMultiplier (c n) * (ComplexConvolutionAnalytic.operator z (2*R) * sqrtMultiplier (c n)) -
      sqrtMultiplier c₀ * (ComplexConvolutionAnalytic.operator z (2*R) * sqrtMultiplier c₀) = _
    rw [mul_assoc, hQ n]
    dsimp [T]
    noncomm_ring
  rw [he]
  have ha1 : ‖T n * L z‖ < ε/2 := h2
  have hb1 : ‖K z * T n‖ < ε/(2*(Real.sqrt D+1)) := h1
  have hb2 : ‖sqrtMultiplier (c n) * (K z * T n)‖ < ε/2 := by
    have hp : 0 < Real.sqrt D+1 := by positivity
    have heq : (Real.sqrt D+1)*(ε/(2*(Real.sqrt D+1))) = ε/2 := by field_simp; ring
    have hb' := mul_lt_mul_of_pos_left hb1 hp
    rw [heq] at hb'
    calc
      ‖sqrtMultiplier (c n) * (K z * T n)‖ ≤ ‖sqrtMultiplier (c n)‖ * ‖K z * T n‖ := norm_mul_le _ _
      _ ≤ (Real.sqrt D+1) * ‖K z * T n‖ := mul_le_mul_of_nonneg_right (by linarith [hS]) (norm_nonneg _)
      _ < ε/2 := hb'
  linarith [norm_add_le (T n * L z) (sqrtMultiplier (c n) * (K z * T n))]
#print axioms OQ14.Packet06WeightedRemainderLimit.weightedRemainder_uniform
end OQ14.Packet06WeightedRemainderLimit
