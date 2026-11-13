import Packet05HomogeneousChartGeometry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet05HomogeneousActualMode
open MeasureTheory Metric Set Maxwell Packet05ChartBasis Packet05ChartLinearEquiv
  Packet05GraphChartMap Packet05PhysicalGraphChart Packet05PhysicalChartBranches
  Packet05GraphSmooth Packet05HomogeneousChartGeometry
open scoped Topology

/-- A genuine complex-frequency volume-kernel mode has a continuous local
representative at every point inside a constant nonzero material phase. -/
theorem actual_homogeneous_neighborhood
    (c : StaticCoefficient.Coefficient) (z : ℂ) (hz : z ≠ 0) (R : ℝ)
    (mode : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (hmode : ComplexConvolutionAnalytic.volumeBlock c z R mode=0)
    (Ω : Set Space) (hΩ : IsOpen Ω) (x : Space) (hx : x ∈ Ω)
    (host : ℂ) (hhost : host ≠ 0)
    (hε : ∀ y ∈ Ω, Packet06MaxwellScalarEquation.epsilon c y = host) :
    let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode) (DynamicVolume.source c mode)
    ∃ (U : Set Space) (reps : Fin 3 → Space → ℂ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧ (∀ j, Continuous (reps j)) ∧
      ∀ j, (fun y => E y j) =ᵐ[volume.restrict U] reps j := by
  classical
  dsimp only
  obtain ⟨g,hg,hgcompact,hpositive⟩ := graph_below x
  let r := ‖x‖+1
  have hr : 0 < r := by dsimp [r]; positivity
  let outer : ContDiffBump (0 : Space) := ⟨r,2*r,hr,by linarith⟩
  let P : Space → Space := physicalFlatMap true 2 g
  let I : Space → Space := fun y => inverseOriented true 2 (graphMap (liftedHeight g) y)
  have hP : Continuous P := physicalFlat_continuous true 2 g (hg.of_le (by decide))
  have hI : Continuous I :=
    (orientedEquiv true 2).symm.toContinuousLinearEquiv.continuous.comp
      (graphMap_contDiff g hg).continuous
  have hIP (y : Space) : I (P y) = y := flat_inverse g y
  have hPI (y : Space) : P (I y) = y := flat_forward g y
  let Vchart : Set Space := ball 0 outer.rIn
  let Wgraph : Set Space := I ⁻¹' (Ω ∩ Vchart) ∩ {y | 0 < y 2}
  let body : Set Space := P ⁻¹' {y | 0 < y 2}
  let p := P x
  have hWopen : IsOpen Wgraph :=
    ((hΩ.inter isOpen_ball).preimage hI).inter
      (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous)
  have hxV : x ∈ Vchart := by
    simp only [Vchart,outer,mem_ball,dist_zero_right,r]
    linarith
  have hpW : p ∈ Wgraph := by
    change I (P x) ∈ Ω ∩ Vchart ∧ 0 < P x 2
    exact ⟨⟨by rw [hIP]; exact hx, by rw [hIP]; exact hxV⟩,hpositive⟩
  have hmapV : ∀ y ∈ Vchart, inverseOriented true 2 y ∈ ball (0 : Space) outer.rIn := by
    intro y hy
    have hid : inverseOriented true 2 y = y := by
      change Packet07BoundaryCoordinates.swap 2 (Packet05ChartOrientation.reflectNormal true y) = y
      ext j
      fin_cases j <;> simp [Packet05ChartOrientation.reflectNormal,Packet07BoundaryCoordinates.swap,Equiv.swap_apply_def]
    simpa only [hid] using hy
  have hmapW : ∀ y ∈ Wgraph, graphMap (liftedHeight g) y ∈ Vchart := by
    intro y hy
    have h := hy.1.2
    have hid : inverseOriented true 2 (graphMap (liftedHeight g) y) = graphMap (liftedHeight g) y := by
      change Packet07BoundaryCoordinates.swap 2 (Packet05ChartOrientation.reflectNormal true _) = _
      ext j
      fin_cases j <;> simp [Packet05ChartOrientation.reflectNormal,Packet07BoundaryCoordinates.swap,Equiv.swap_apply_def]
    simpa only [I,hid] using h
  have hside : ∀ y ∈ Wgraph, inverseOriented true 2 (graphMap (liftedHeight g) y) ∈ body ↔ 0 < y 2 := by
    intro y hy
    change 0 < P (I y) 2 ↔ 0 < y 2
    rw [hPI]
  have hmaterial : ∀ y ∈ Wgraph, Packet06MaxwellScalarEquation.epsilon c
      (inverseOriented true 2 (graphMap (liftedHeight g) y)) =
      host * (if inverseOriented true 2 (graphMap (liftedHeight g) y) ∈ body then (1+(0 : ℝ) : ℂ) else 1) := by
    intro y hy
    rw [hε (I y) hy.1.1]
    split_ifs <;> simp
  obtain ⟨T,lower,upper,hT,hpT,hTW,hl,hu,hle,hue⟩ :=
    Packet05OpenModeChart.open_mode_chart c z hz R mode hc hmode body host hhost 0 (by norm_num) outer true 2 g hg hgcompact
      Vchart Wgraph hWopen p hpW hmapV hmapW hside hmaterial
  let U : Set Space := P ⁻¹' (T ∩ {y | 0 < y 2})
  have hUopen : IsOpen U := (hT.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous)).preimage hP
  have hxU : x ∈ U := ⟨hpT,hpositive⟩
  have hUΩ : U ⊆ Ω := by
    intro y hy
    have h := hTW hy.1
    change I (P y) ∈ Ω ∩ Vchart ∧ _ at h
    rw [hIP] at h
    exact h.1.1
  exact ⟨U,upper,hUopen,hxU,hUΩ,hu,hue⟩

#print axioms OQ14.Packet05HomogeneousActualMode.actual_homogeneous_neighborhood
end OQ14.Packet05HomogeneousActualMode
