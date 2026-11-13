import Packet07DrivenUniformCollarPhase
import Packet05HomogeneousChartGeometry

/-! Fixed artificial graph charts for homogeneous portions of the reference
collar; the material law holds simultaneously for the late family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenUniformHomogeneousChart
open Set Filter Metric Maxwell Packet07PlanarSetup Packet07DrivenUniformCollarChart
  Packet07DrivenUniformCollarPhase Packet05ChartBasis Packet05ChartLinearEquiv
  Packet05GraphChartMap Packet05PhysicalGraphChart Packet05PhysicalChartBranches
  Packet05GraphSmooth Packet05HomogeneousChartGeometry
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

theorem fixed_homogeneous_chart {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ} (g : Setup N Pset d t)
    (r b : ℝ) (j0 : ℕ)
    (hstable : ∀ᶠ j : ℕ in atTop, ∀ (i : Fin N) (x : Space),
      r < ‖x-g.centers i‖ → ‖x-g.centers i‖ < b → (x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j ↔ x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0))
    (i : Fin N) (Ω : Set Space) (hΩopen : IsOpen Ω) (hΩ : Ω ⊆ annulus g i r b)
    (inside : Prop) (hphase : ∀ x ∈ Ω, x ∈ CommonBinaryInterface.body g.dataFamily g.radii g.centers j0 ↔ inside)
    (x : Space) (hx : x ∈ Ω) (χ : ContDiffBump (0 : Space)) (hxχ : x ∈ ball (0 : Space) χ.rIn) :
    ∃ (G : Plane → ℝ) (T bodyChart : Set Space), ContDiff ℝ 4 G ∧ HasCompactSupport G ∧
      IsOpen T ∧ physicalFlatMap true 2 G x ∈ T ∧ 0 < physicalFlatMap true 2 G x 2 ∧
      (∀ y ∈ T, inverseOriented true 2 (graphMap (liftedHeight G) y) ∈ ball (0 : Space) χ.rIn) ∧
      (∀ y ∈ T, inverseOriented true 2 (graphMap (liftedHeight G) y) ∈ bodyChart ↔ 0 < y 2) ∧
      ∀ᶠ j : ℕ in atTop, ∀ y ∈ T,
        Packet06MaxwellScalarEquation.epsilon (g.rounded j)
          (inverseOriented true 2 (graphMap (liftedHeight G) y)) =
          ((1 : ℂ)*(by classical exact if inside then (1+d : ℂ) else 1)) *
            (by classical exact if inverseOriented true 2 (graphMap (liftedHeight G) y) ∈ bodyChart
              then (1+(0 : ℝ) : ℂ) else 1) := by
  classical
  obtain ⟨G,hG,hGc,hpositive⟩ := graph_below x
  let P : Space → Space := physicalFlatMap true 2 G
  let I : Space → Space := fun y => inverseOriented true 2 (graphMap (liftedHeight G) y)
  have hP : Continuous P := physicalFlat_continuous true 2 G (hG.of_le (by decide))
  have hI : Continuous I := (orientedEquiv true 2).symm.toContinuousLinearEquiv.continuous.comp
    (graphMap_contDiff G hG).continuous
  let T : Set Space := I ⁻¹' (Ω ∩ ball (0 : Space) χ.rIn) ∩ {y | 0 < y 2}
  let bodyChart : Set Space := P ⁻¹' {y | 0 < y 2}
  have hT : IsOpen T := ((hΩopen.inter isOpen_ball).preimage hI).inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous)
  have hxT : P x ∈ T := ⟨⟨by simpa [I,P,flat_inverse] using hx,
    by simpa [I,P,flat_inverse] using hxχ⟩,hpositive⟩
  refine ⟨G,T,bodyChart,hG,hGc,hT,hxT,hpositive,?_,?_,?_⟩
  · intro y hy
    exact hy.1.2
  · intro y hy
    change 0 < P (I y) 2 ↔ 0 < y 2
    rw [show P (I y)=y from flat_forward G y]
  · filter_upwards [eventually_constant_on_phase g r b j0 hstable i Ω hΩ inside hphase] with j hj y hy
    rw [hj (I y) hy.1.1]
    split_ifs <;> simp

end OQ14.Packet07DrivenUniformHomogeneousChart
#print axioms OQ14.Packet07DrivenUniformHomogeneousChart.fixed_homogeneous_chart
