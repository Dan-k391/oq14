import Packet05ReferencePhaseNeighborhood
import Packet05PhaseWeightBound

/-! Every point of a fixed collar has one fixed C⁴ graph chart with an
exact eventual binary material law for the actual rounded family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05FixedCollarAllCharts
open Set Filter Metric Maxwell Packet06ConcreteModalRounding Packet05FixedCollarChart
  Packet05FixedHomogeneousChart Packet05ReferencePhaseNeighborhood Packet05ActualFlatNeighborhood
  Packet05ChartBasis Packet05GraphChartMap Packet05PhysicalGraphChart Packet05PhysicalChartBranches
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

theorem fixed_chart_at_point {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (r b : ℝ) (hb : b < g.radius) (j0 : ℕ)
    (hstable : ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.center i‖ → ‖x-g.center i‖ < b → (x ∈ body g j ↔ x ∈ body g j0))
    (hcert : ∀ x ∈ frontier (body g j0), ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ body g j0 ↔ 0 < F y))
    (i : Fin N) (x : Space) (hx : x ∈ annulus g i r b)
    (χ : ContDiffBump (0 : Space)) (hxχ : x ∈ ball (0 : Space) χ.rIn) :
    ∃ (up : Bool) (axis : Fin 3) (G : Plane → ℝ) (T bodyChart : Set Space) (host : ℂ) (d : ℝ),
      ContDiff ℝ 4 G ∧ HasCompactSupport G ∧ IsOpen T ∧ physicalFlatMap up axis G x ∈ T ∧
      host ≠ 0 ∧ 0 ≤ d ∧
      (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ ball (0 : Space) χ.rIn) ∧
      (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ bodyChart ↔ 0 < y 2) ∧
      ∀ᶠ j : ℕ in atTop, ∀ y ∈ T,
        Packet06MaxwellScalarEquation.epsilon (rounded n hn g η hη j)
          (inverseOriented up axis (graphMap (liftedHeight G) y)) =
          host * (by classical exact if inverseOriented up axis (graphMap (liftedHeight G) y) ∈ bodyChart
            then (1+d : ℂ) else 1) := by
  classical
  have hn0 : (n^2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (sq_pos_of_pos (by linarith : 0 < n)))
  by_cases hfront : x ∈ frontier (body g j0)
  · obtain ⟨up,axis,G,T,hG,hGc,hT,hxT,_,hmap,hside,hmat⟩ :=
      fixed_collar_chart n hn g η hη r b hb j0 hstable i x hx hfront (hcert x hfront) χ hxχ
    exact ⟨up,axis,G,T,body g j0,(n^2 : ℂ),η,hG,hGc,hT,hxT,hn0,hη,hmap,hside,hmat⟩
  · obtain ⟨U,inside,hU,hxU,hUann,hphase⟩ :=
      phase_neighborhood (body g j0) (annulus g i r b) (annulus_open g i r b) x hx hfront
    obtain ⟨G,T,bodyChart,hG,hGc,hT,hxT,_,hmap,hside,hmat⟩ :=
      fixed_homogeneous_chart n hn g η hη r b hb j0 hstable i U hU hUann inside hphase x hxU χ hxχ
    let host : ℂ := (n^2 : ℂ)*(if inside then (1+η : ℂ) else 1)
    have hhost : host ≠ 0 := by
      dsimp [host]
      apply mul_ne_zero hn0
      split_ifs
      · exact_mod_cast (ne_of_gt (show 0 < 1+η by linarith))
      · norm_num
    exact ⟨true,2,G,T,bodyChart,host,0,hG,hGc,hT,hxT,hhost,le_rfl,hmap,hside,hmat⟩

end OQ14.Packet05FixedCollarAllCharts
#print axioms OQ14.Packet05FixedCollarAllCharts.fixed_chart_at_point
