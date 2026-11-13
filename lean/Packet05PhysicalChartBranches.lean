import Packet05ActualChartPhaseBranches

/-! Transport continuous graph-phase branches back to the actual physical
coordinates, preserving a.e. equality under the signed chart and shear. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05PhysicalChartBranches
open MeasureTheory Set OQ14.Maxwell OQ14.Packet05ChartOrientation
  OQ14.Packet05ChartOrientationMeasure OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv
  OQ14.Packet05ChartElectricIdentity OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphSmooth OQ14.Packet05GraphVolume
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def physicalFlatMap (up : Bool) (i : Fin 3) (g : Plane → ℝ) (y : Space) : Space :=
  inverseGraphMap (liftedHeight g) (orientedLinear up i y)

theorem inverse_graph_measure_preserving (g : Plane → ℝ) (hg : Continuous g) :
    MeasurePreserving (inverseGraphMap (liftedHeight g)) (volume : Measure Space) volume := by
  have hm := graph_map_volume_preserving (-g) hg.neg
  convert hm using 1
  funext x
  simp [graphMap,inverseGraphMap,liftedHeight,sub_eq_add_neg,neg_smul]

theorem physicalFlat_measure_preserving (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : Continuous g) :
    MeasurePreserving (physicalFlatMap up i g) (volume : Measure Space) volume :=
  (inverse_graph_measure_preserving g hg).comp (oriented_coordinates_measure_preserving up i)

theorem physicalFlat_continuous (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) :
    Continuous (physicalFlatMap up i g) :=
  (inverseGraphMap_contDiff g hg).continuous.comp (orientedLinear up i).toContinuousLinearMap.continuous

theorem physical_chart_branches (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (T : Set Space) (hT : MeasurableSet T) (E : Field) (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ j, Continuous (reps j))
    (hrep : ∀ j, (fun x => orientedElectric up i g E x j) =ᵐ[volume.restrict T] reps j) :
    ∃ physical : Fin 3 → Space → ℂ, (∀ j, Continuous (physical j)) ∧
      ∀ j, (fun y => E y j) =ᵐ[volume.restrict (physicalFlatMap up i g ⁻¹' T)] physical j := by
  let p := physicalFlatMap up i g
  let physical : Fin 3 → Space → ℂ := fun j y =>
    (chartSign up (Equiv.swap i 2 j) : ℂ) * reps (Equiv.swap i 2 j) (p y)
  refine ⟨physical,?_,?_⟩
  · intro j
    exact continuous_const.mul ((hreps _).comp (physicalFlat_continuous up i g hg))
  · intro j
    let k := Equiv.swap i 2 j
    have hr := (ae_restrict_iff' hT).mp (hrep k)
    have hp := (physicalFlat_measure_preserving up i g hg.continuous).quasiMeasurePreserving.ae hr
    have hset : MeasurableSet (p ⁻¹' T) := hT.preimage (physicalFlat_continuous up i g hg).measurable
    apply (ae_restrict_iff' hset).mpr
    filter_upwards [hp] with y hy hyT
    have hh := hy hyT
    have hback : inverseOriented up i (graphMap (liftedHeight g) (p y)) = y := by
      change inverseOriented up i (graphMap (liftedHeight g)
        (inverseGraphMap (liftedHeight g) (orientedLinear up i y))) = y
      rw [graph_map_right_inverse _ (liftedHeight_normal_invariant g)]
      exact inverse_oriented_left up i y
    have hidx : Equiv.swap i 2 k = j := Equiv.swap_apply_self _ _ _
    change (chartSign up k : ℂ) * E (inverseOriented up i (graphMap (liftedHeight g) (p y)))
      (Equiv.swap i 2 k) = reps k (p y) at hh
    rw [hback,hidx] at hh
    change E y j = (chartSign up k : ℂ) * reps k (p y)
    rw [← hh]
    cases up
    · by_cases hk : k = 2 <;> simp [chartSign,hk]
    · simp [chartSign]

end OQ14.Packet05PhysicalChartBranches
#print axioms OQ14.Packet05PhysicalChartBranches.inverse_graph_measure_preserving
#print axioms OQ14.Packet05PhysicalChartBranches.physicalFlat_measure_preserving
#print axioms OQ14.Packet05PhysicalChartBranches.physicalFlat_continuous
#print axioms OQ14.Packet05PhysicalChartBranches.physical_chart_branches
