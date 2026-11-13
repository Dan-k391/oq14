import Packet06MaterialDynamic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06MaterialPencil
open Filter Set MeasureTheory Metric OQ14.StaticCoefficient OQ14.Packet06MaterialStatic
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev Space := FourierL2.Space

def compactPart (c : Coefficient) (z : ℂ) (R : ℝ) : V →L[ℂ] V :=
  Ring.inverse (staticBlock c) * ComplexConvolutionAnalytic.operator z (2*R) * materialMultiplier c

theorem compactPart_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0)
    (A : Set ℂ) (hA : IsCompact A) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ A, ‖compactPart (c n) z R - compactPart c₀ z R‖ < ε := by
  have hD : 0 ≤ D := (bound_nonnegative c₀).trans hb₀
  let K : ℂ → V →L[ℂ] V := fun z => ComplexConvolutionAnalytic.operator z (2*R) * materialMultiplier c₀
  let S : ℕ → V →L[ℂ] V := fun n => Ring.inverse (staticBlock (c n)) - Ring.inverse (staticBlock c₀)
  have hbS (n : ℕ) : ‖S n‖ ≤ 2*(1+D) := by
    exact (norm_sub_le _ _).trans (by
      have h1 : ‖Ring.inverse (staticBlock (c n))‖ ≤ 1+D :=
        (staticBlock_inverse_norm_le (c n)).trans (add_le_add_left (hb n) 1)
      have h2 : ‖Ring.inverse (staticBlock c₀)‖ ≤ 1+D :=
        (staticBlock_inverse_norm_le c₀).trans (add_le_add_left hb₀ 1)
      linarith)
  have hsS (f : V) : Tendsto (fun n => S n f) atTop (𝓝 0) := by
    change Tendsto (fun n => Ring.inverse (staticBlock (c n)) f - Ring.inverse (staticBlock c₀) f) atTop (𝓝 0)
    simpa using (staticBlock_inverse_strong c c₀ D hb hb₀ ha f).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => Ring.inverse (staticBlock c₀) f) atTop (𝓝 (Ring.inverse (staticBlock c₀) f)))
  have hcont : ContinuousOn K A := by
    apply Continuous.continuousOn
    exact ((ComplexConvolutionAnalytic.operator_differentiable (2*R) (by positivity)).clm_comp
      (differentiable_const (materialMultiplier c₀))).continuous
  have hcompact (z : ℂ) : IsCompactOperator (K z) := by
    have h := (ComplexConvolutionAnalytic.source_operator_compact c₀ z R hc₀).comp_clm (sqrtMultiplier c₀)
    simpa only [K, materialMultiplier, ← ContinuousLinearMap.mul_def, mul_assoc] using h
  have hsecond := Packet06StrongCompact.compact_family_uniform S (2*(1+D)) (by positivity)
    hbS hsS K A hA hcont (fun z _ => hcompact z)
  have hfirst := Packet06MaterialDynamic.dynamic_material_uniform c c₀ D R hR hb hb₀ ha hc hc₀ A hA
  intro ε hε
  have hδ : 0 < ε / (2*(1+D)) := by positivity
  filter_upwards [hfirst (ε / (2*(1+D))) hδ, hsecond (ε/2) (by positivity)] with n hn1 hn2 z hz
  have h1 := hn1 z hz
  have h2 := hn2 z hz
  have hinv : ‖Ring.inverse (staticBlock (c n))‖ ≤ 1+D :=
    (staticBlock_inverse_norm_le (c n)).trans (by linarith [hb n])
  have he : compactPart (c n) z R - compactPart c₀ z R =
      Ring.inverse (staticBlock (c n)) * (ComplexConvolutionAnalytic.operator z (2*R) *
        (materialMultiplier (c n) - materialMultiplier c₀)) + S n * K z := by
    dsimp [compactPart, S, K]
    noncomm_ring
  rw [he]
  have hn := norm_add_le (Ring.inverse (staticBlock (c n)) * (ComplexConvolutionAnalytic.operator z (2*R) *
        (materialMultiplier (c n) - materialMultiplier c₀))) (S n * K z)
  have hm := norm_mul_le (Ring.inverse (staticBlock (c n))) (ComplexConvolutionAnalytic.operator z (2*R) *
        (materialMultiplier (c n) - materialMultiplier c₀))
  have hx : ‖ComplexConvolutionAnalytic.operator z (2*R) *
        (materialMultiplier (c n) - materialMultiplier c₀)‖ < ε/(2*(1+D)) := h1
  have hy : ‖S n * K z‖ < ε/2 := h2
  have hm' : ‖Ring.inverse (staticBlock (c n)) * (ComplexConvolutionAnalytic.operator z (2*R) *
        (materialMultiplier (c n) - materialMultiplier c₀))‖ < ε/2 := by
    have hp : 0 < 1+D := by positivity
    have := mul_lt_mul_of_pos_left hx hp
    have hid : (1+D)*(ε/(2*(1+D))) = ε/2 := by field_simp; ring
    rw [hid] at this
    exact lt_of_le_of_lt (hm.trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))) this
  linarith
#print axioms OQ14.Packet06MaterialPencil.compactPart_uniform
end OQ14.Packet06MaterialPencil
