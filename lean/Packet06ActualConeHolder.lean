import Packet06ComplexConeSystem
import Packet06GreenHolderEndpoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ActualConeHolder
open MeasureTheory Metric OQ14.Maxwell OQ14.Packet06ComplexConeSystem
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev V := VectorFourier.VectorL2

theorem correction_holder (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0)
    (p : ConicalStaticVolume.Data) (b : ℝ) (_hb0 : 0 ≤ b) (hb : b < p.cutoff.rIn) (hb1 : b ≤ 1)
    (center : Maxwell.Space) (α : ℝ) (hα : α ≠ 0)
    (hball : closedBall center b ⊆ closedBall 0 T)
    (hmatch : ∀ y ∈ ball (0 : Maxwell.Space) b, 1+c.value (VectorFourier.coordinateMap (y+center)) =
      α * ConicalLocalGauss.epsilon p y)
    (Z R L : ℝ) (hZ : ‖z‖ ≤ Z) (hR : 0 ≤ R) (hS : 0 ≤ S) (_hL : 0 ≤ L)
    (hcenter : ‖center‖ ≤ R)
    (hinside : ∀ x ∈ closedBall (0 : Maxwell.Space) b, ‖x+center‖ ≤ R)
    (hsource : ∀ i, ‖NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) i‖ ≤ L) :
    ∀ i x, x ∈ closedBall (0 : Maxwell.Space) b →
      ‖(system c z hz S T hST hplus u hc hu p b hb center α hα hball hmatch).correction i x-
        (system c z hz S T hST hplus u hc hu p b hb center α hα hball hmatch).correction i 0‖ ≤
      (Z^2*L*Packet06GreenHolderEndpoint.constant Z R S)*‖x‖^(1/2 : ℝ) := by
  intro i x hx
  have hxb : x ∈ ball (0 : Maxwell.Space) p.cutoff.rIn := closedBall_subset_ball hb hx
  have h0b : (0 : Maxwell.Space) ∈ ball 0 p.cutoff.rIn := by
    have hpos : 0 < p.cutoff.rIn := p.cutoff.rIn_pos
    simpa using hpos
  have hbx := (ConicalGradientGraph.bump_inner p.cutoff x hxb).1
  have hbz := (ConicalGradientGraph.bump_inner p.cutoff 0 h0b).1
  change ‖ConicalGradientGraph.bump p.cutoff x * Packet06ComplexPotential.correction z (DynamicVolume.source c u) (x+center) i -
    ConicalGradientGraph.bump p.cutoff 0 * Packet06ComplexPotential.correction z (DynamicVolume.source c u) (0+center) i‖ ≤ _
  rw [hbx,hbz]
  simp only [one_mul,zero_add,Packet06ComplexPotential.correction]
  have hxnorm : ‖x‖ ≤ b := by simpa using hx
  have hsmall : ‖(x+center)-center‖ ≤ 1 := by simpa using hxnorm.trans hb1
  have h := Packet06GreenHolderEndpoint.actual_response_holder z Z R S hZ hR hS
    (DynamicVolume.source c u i) (NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) i)
    (StaticNewton.material_source_ae c u i) (DynamicVolume.source_zero c u S hc i)
    (x+center) center (hinside x hx) hcenter hsmall
  rw [dist_eq_norm] at h
  have hsqrt : Real.sqrt (dist (x+center) center) = ‖x‖^(1/2 : ℝ) := by
    rw [dist_eq_norm,add_sub_cancel_right,Real.sqrt_eq_rpow]
  rw [hsqrt] at h
  have hc0 : 0 ≤ Packet06GreenHolderEndpoint.constant Z R S := Real.sqrt_nonneg _
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hsource i) (sq_nonneg Z)) hc0)
    (Real.rpow_nonneg (norm_nonneg x) (1/2 : ℝ))
  exact h.trans hm
#print axioms OQ14.Packet06ActualConeHolder.correction_holder
end OQ14.Packet06ActualConeHolder
