import Packet06MaterialCompact
import RestrictedTEParitySandwich
import ComplexConvolutionAnalytic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06MaterialDynamic
open Filter Set MeasureTheory Metric OQ14.StaticCoefficient OQ14.Packet06MaterialStatic
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev Space := FourierL2.Space
abbrev ballCoefficient := RestrictedTEParitySandwich.ballCoefficient

theorem ball_cut_sqrt (c : Coefficient) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    sqrtMultiplier (ballCoefficient R) * sqrtMultiplier c = sqrtMultiplier c := by
  ext f
  filter_upwards [sqrtMultiplier_ae (ballCoefficient R) (sqrtMultiplier c f),
    sqrtMultiplier_ae c f] with ξ hq hc'
  change sqrtMultiplier (ballCoefficient R) (sqrtMultiplier c f) ξ = sqrtMultiplier c f ξ
  rw [hq, hc']
  let x : Space := VectorFourier.coordinateMap.symm ξ
  have hξ : VectorFourier.coordinateMap x = ξ := by simp [x]
  by_cases hx : x ∈ closedBall 0 R
  · have hball : (ballCoefficient R).value ξ = 1 := by
      rw [← hξ, RestrictedTEParitySandwich.ballCoefficient_value]
      simp [hx]
    simp [hball]
  · have hz : c.value ξ = 0 := by rw [← hξ]; exact hc x hx
    simp [hz]

theorem dynamic_material_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0)
    (A : Set ℂ) (hA : IsCompact A) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ A,
      ‖(ComplexConvolutionAnalytic.operator z (2*R)).comp
        (materialMultiplier (c n) - materialMultiplier c₀)‖ < ε := by
  let Q := sqrtMultiplier (ballCoefficient R)
  let K : ℂ → V →L[ℂ] V := fun z => (ComplexConvolutionAnalytic.operator z (2*R)).comp Q
  have hcont : ContinuousOn K A := by
    apply Continuous.continuousOn
    exact ((ComplexConvolutionAnalytic.operator_differentiable (2*R) (by positivity)).clm_comp
      (differentiable_const Q)).continuous
  have hcompact (z : ℂ) : IsCompactOperator (K z) := by
    apply ComplexConvolutionAnalytic.source_operator_compact (ballCoefficient R) z R
    intro x hx
    rw [RestrictedTEParitySandwich.ballCoefficient_value]
    simp [hx]
  have hQ (c' : Coefficient) (hc' : ∀ x : Space, x ∉ closedBall 0 R →
      c'.value (VectorFourier.coordinateMap x) = 0) : Q * materialMultiplier c' = materialMultiplier c' := by
    change sqrtMultiplier (ballCoefficient R) * (sqrtMultiplier c' * sqrtMultiplier c') = sqrtMultiplier c' * sqrtMultiplier c'
    rw [← mul_assoc, ball_cut_sqrt c' R hc']
  have h := Packet06MaterialCompact.compact_material_family_uniform c c₀ D hb hb₀ ha K A hA hcont (fun z _ => hcompact z)
  intro ε hε
  filter_upwards [h ε hε] with n hn z hz
  have hn' := hn z hz
  have he : (K z).comp (materialMultiplier (c n) - materialMultiplier c₀) =
      (ComplexConvolutionAnalytic.operator z (2*R)).comp
        (materialMultiplier (c n) - materialMultiplier c₀) := by
    change (ComplexConvolutionAnalytic.operator z (2*R)) * Q *
      (materialMultiplier (c n) - materialMultiplier c₀) = _
    rw [mul_assoc, mul_sub, hQ (c n) (hc n), hQ c₀ hc₀]
    rfl
  simpa only [he] using hn'
#print axioms OQ14.Packet06MaterialDynamic.ball_cut_sqrt
#print axioms OQ14.Packet06MaterialDynamic.dynamic_material_uniform
end OQ14.Packet06MaterialDynamic
