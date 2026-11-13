import Packet07DrivenUniformReference
import Packet05ActualFlatNeighborhood
import Packet06MaxwellScalarEquation

/-! A single actual reference-body chart and exact binary material law work
on a fixed open annulus for every sufficiently late rounded mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenUniformCollarChart
open Set Filter Metric Maxwell Packet07PlanarSetup Packet05ActualOrientedGraph
  Packet05ActualFlatNeighborhood Packet05ChartBasis Packet05GraphChartMap Packet05PhysicalGraphChart
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

def annulus {N : ℕ} {P : Set Plane} {d t : ℝ} (g : Setup N P d t)
    (i : Fin N) (r b : ℝ) : Set Space := {x | r < ‖x-g.centers i‖ ∧ ‖x-g.centers i‖ < b}

theorem annulus_open {N : ℕ} {P : Set Plane} {d t : ℝ} (g : Setup N P d t)
    (i : Fin N) (r b : ℝ) : IsOpen (annulus g i r b) := by
  exact (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)

theorem fixed_collar_chart {N : ℕ} {P : Set Plane} {d t : ℝ} (g : Setup N P d t)
    (r b : ℝ) (j0 : ℕ)
    (hstable : ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.centers i‖ → ‖x-g.centers i‖ < b → (x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j ↔ x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0))
    (i : Fin N) (x : Space) (hx : x ∈ annulus g i r b) (hfront : x ∈ frontier (CommonBinaryInterface.body g.dataFamily g.radii g.centers j0))
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0 ↔ 0 < F y))
    (χ : ContDiffBump (0 : Space)) (hxχ : x ∈ ball (0 : Space) χ.rIn) :
    ∃ (up : Bool) (axis : Fin 3) (G : Plane → ℝ) (T : Set Space),
      ContDiff ℝ 4 G ∧ HasCompactSupport G ∧ IsOpen T ∧ chartPoint up axis G x ∈ T ∧
      chartPoint up axis G x 2 = 0 ∧
      (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ ball (0 : Space) χ.rIn) ∧
      (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight G) y) ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0 ↔ 0 < y 2) ∧
      ∀ᶠ j : ℕ in atTop, ∀ y ∈ T,
        Packet06MaxwellScalarEquation.epsilon (g.rounded j)
          (inverseOriented up axis (graphMap (liftedHeight G) y)) =
          (1 : ℂ)*(by classical exact if inverseOriented up axis (graphMap (liftedHeight G) y) ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0
            then (1+d : ℂ) else 1) := by
  classical
  obtain ⟨up,axis,G,hG,hGc,hzero,hside⟩ := actual_oriented_graph (CommonBinaryInterface.body g.dataFamily g.radii g.centers j0) x hfront hcert
  let Ω : Set Space := annulus g i r b ∩ ball (0 : Space) χ.rIn
  have hΩ : IsOpen Ω := (annulus_open g i r b).inter isOpen_ball
  obtain ⟨δ,hδ,hpoint,hflat⟩ := actual_flat_neighborhood (CommonBinaryInterface.body g.dataFamily g.radii g.centers j0) Ω x hΩ ⟨hx,hxχ⟩ up axis G hG hzero hside
  let T := ball (chartPoint up axis G x) δ
  refine ⟨up,axis,G,T,hG,hGc,isOpen_ball,mem_ball_self hδ,hpoint,?_,?_,?_⟩
  · intro y hy
    exact (hflat y hy).1.2
  · intro y hy
    exact (hflat y hy).2
  · filter_upwards [hstable] with j hj y hy
    let z := inverseOriented up axis (graphMap (liftedHeight G) y)
    have hz := (hflat y hy).1.1
    have hs := hj i z hz.1 hz.2
    have he := CommonBinaryInterface.coefficient_body g.dataFamily g.radii g.centers d
      g.contrast_pos.le g.contrast_bound g.radii_pos g.radii_outer g.outer_sep d
      (fun _ => g.contrast_eq) j z
    change (g.rounded j).value (VectorFourier.coordinateMap z) =
      (if z ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j then d else 0) at he
    change Packet06MaxwellScalarEquation.epsilon (g.rounded j) z =
      (1 : ℂ)*(if z ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0 then (1+d : ℂ) else 1)
    unfold Packet06MaxwellScalarEquation.epsilon
    rw [he]
    by_cases hbody : z ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0
    · have hjbody : z ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j := hs.mpr hbody
      simp [hbody,hjbody]
    · have hjbody : z ∉ CommonBinaryInterface.body g.dataFamily g.radii g.centers j := fun h => hbody (hs.mp h)
      simp [hbody,hjbody]

end OQ14.Packet07DrivenUniformCollarChart
#print axioms OQ14.Packet07DrivenUniformCollarChart.annulus_open
#print axioms OQ14.Packet07DrivenUniformCollarChart.fixed_collar_chart
