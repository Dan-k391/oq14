import Packet05UniformScalarGraph
import Packet05UniformMaterialCorrection

/-! Actual material families supply uniform scalar potential and graph-gradient bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05UniformMaterialScalarGraph
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.ConicalGradientGraph
  OQ14.Packet05UniformScalarGraph OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphPullback OQ14.Packet05ChartWeakGradient OQ14.Packet05ChartWeakDivergence
  OQ14.Packet05GraphH1Pullback
abbrev V := OQ14.VectorFourier.VectorL2
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem material_family_scalar_graph {A : Type*}
    (c : A → OQ14.StaticCoefficient.Coefficient) (z : A → ℂ) (u : A → V)
    (S Z B L Bs : ℝ) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hc : ∀ a x, x ∉ closedBall (0 : Maxwell.Space) S → (c a).value (OQ14.VectorFourier.coordinateMap x)=0)
    (hb : ∀ a, (c a).bound ≤ B) (hz : ∀ a, ‖z a‖ ≤ Z) (hu : ∀ a, ‖u a‖ ≤ L)
    (χ : ContDiffBump (0 : Maxwell.Space)) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (hBs : ∀ i x, ‖slopeC g i x‖ ≤ Bs) (up : Bool) (axis : Fin 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a,
      let F := OQ14.StaticCoefficient.sqrtMultiplier (c a) (u a)
      let ρ := OQ14.DynamicVolume.source (c a) (u a)
      let U := OQ14.Packet06ComplexConePotential.potentialData (z a) S F ρ
        (OQ14.DynamicVolume.source_zero (c a) (u a) S (hc a)) (OQ14.StaticNewton.material_source_ae (c a) (u a))
      let v := pullback g hg.continuous (chartPull up axis (value χ U))
      let C := pulledGradient g hg (chartVector up axis (ConicalGradientGraph.gradient χ U)) (fun _ => Bs) hBs
      ‖v‖ ≤ K ∧ ∀ i, ‖C i‖ ≤ K := by
  obtain ⟨K,hK,hall⟩ := uniform_actual_scalar_graph χ S Z Bs hS hZ g hg hBs up axis
  refine ⟨K*(Real.sqrt B*L),mul_nonneg hK (mul_nonneg (Real.sqrt_nonneg _) hL),?_⟩
  intro a
  let F := OQ14.StaticCoefficient.sqrtMultiplier (c a) (u a)
  let ρ := OQ14.DynamicVolume.source (c a) (u a)
  have hF : ‖F‖ ≤ Real.sqrt B*L := by
    exact (OQ14.StaticCoefficient.applySqrt_norm (c a) (u a)).trans
      (mul_le_mul (Real.sqrt_le_sqrt (hb a)) (hu a) (norm_nonneg _) (Real.sqrt_nonneg _))
  have hg := hall (z a) (hz a) F ρ
    (OQ14.DynamicVolume.source_integrable (c a) (u a) S (hc a))
    (OQ14.StaticNewton.material_source_ae (c a) (u a))
    (OQ14.DynamicVolume.source_zero (c a) (u a) S (hc a))
  have hbnd := mul_le_mul_of_nonneg_left hF hK
  exact ⟨hg.1.trans hbnd,fun i => (hg.2 i).trans hbnd⟩

end OQ14.Packet05UniformMaterialScalarGraph
#print axioms OQ14.Packet05UniformMaterialScalarGraph.material_family_scalar_graph
