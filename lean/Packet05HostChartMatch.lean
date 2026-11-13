import Packet05HostNormalization

/-! Local positive-host contrast becomes the unit-background flat jump
almost everywhere after normalizing the physical Gauss flux. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05HostChartMatch
open MeasureTheory Set OQ14.Maxwell OQ14.ConicalJunctionPhysical
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart OQ14.Packet05ChartBasis
  OQ14.Packet05FlatWeight OQ14.Packet05LocalDerivative
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem host_chart_match_ae (c : StaticCoefficient.Coefficient) (body : Set Maxwell.Space)
    (host : ℂ) (hhost : host ≠ 0) (d : ℝ) (up : Bool) (i : Fin 3)
    (g : Plane → ℝ) (W : Set Maxwell.Space)
    (hside : ∀ x ∈ W, inverseOriented up i (graphMap (liftedHeight g) x) ∈ body ↔ 0 < x 2)
    (hmaterial : ∀ x ∈ W, Packet06MaxwellScalarEquation.epsilon c
      (inverseOriented up i (graphMap (liftedHeight g) x)) =
        host * (by classical exact if inverseOriented up i (graphMap (liftedHeight g) x) ∈ body
          then (1+d : ℂ) else 1)) :
    ∀ᵐ x ∂volume, x ∈ W → host⁻¹ * Packet06MaxwellScalarEquation.epsilon c
      (inverseOriented up i (graphMap (liftedHeight g) x)) = weight d x := by
  classical
  have hn : ∀ᵐ x : Maxwell.Space ∂volume, x 2 ≠ 0 := by
    rw [ae_iff]
    simpa using interface_plane_null
  filter_upwards [hn] with x hx hW
  rw [hmaterial x hW]
  by_cases hneg : x 2 < 0
  · have hnot : inverseOriented up i (graphMap (liftedHeight g) x) ∉ body := by
      intro hy
      have := (hside x hW).mp hy
      linarith
    simp [hnot,weight,FlatDifferenceCoercivity.dielectric,hneg,hhost]
  · have hpos : 0 < x 2 := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hx)
    have hin := (hside x hW).mpr hpos
    simp [hin,weight,FlatDifferenceCoercivity.dielectric,hneg,hhost]

end OQ14.Packet05HostChartMatch
#print axioms OQ14.Packet05HostChartMatch.host_chart_match_ae
