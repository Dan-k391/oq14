import Packet05PhysicalChartBranches

/-! Quantitative chart representatives return to the physical coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05QuantitativePhysicalChart
open MeasureTheory Set Maxwell Packet05ChartOrientation Packet05ChartOrientationMeasure
  Packet05ChartBasis Packet05ChartLinearEquiv Packet05ChartElectricIdentity
  Packet05GraphChartMap Packet05PhysicalGraphChart Packet05GraphSmooth Packet05GraphVolume
  Packet05PhysicalChartBranches
abbrev Plane := ConicalSmoothJunction.Plane

theorem quantitative_physical_chart_branches (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (T : Set Space) (hT : MeasurableSet T) (E : Field) (reps : Fin 3 → Space → ℂ)
    (hreps : ∀ j, Continuous (reps j))
    (hrep : ∀ j, (fun x => orientedElectric up i g E x j) =ᵐ[volume.restrict T] reps j)
    (B : ℝ) (hbound : ∀ j x, x ∈ T → ‖reps j x‖ ≤ B) :
    ∃ physical : Fin 3 → Space → ℂ, (∀ j, Continuous (physical j)) ∧
      (∀ j, (fun y => E y j) =ᵐ[volume.restrict (physicalFlatMap up i g ⁻¹' T)] physical j) ∧
      ∀ j y, y ∈ physicalFlatMap up i g ⁻¹' T → ‖physical j y‖ ≤ B := by
  let p := physicalFlatMap up i g
  let physical : Fin 3 → Space → ℂ := fun j y =>
    (chartSign up (Equiv.swap i 2 j) : ℂ) * reps (Equiv.swap i 2 j) (p y)
  refine ⟨physical,?_,?_,?_⟩
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

  · intro j y hy
    change ‖(chartSign up (Equiv.swap i 2 j) : ℂ) * reps (Equiv.swap i 2 j) (p y)‖ ≤ B
    have hh := hbound (Equiv.swap i 2 j) (p y) hy
    cases up
    · by_cases hk : Equiv.swap i 2 j = 2 <;> simpa [chartSign,hk] using hh
    · simpa [chartSign] using hh

end OQ14.Packet05QuantitativePhysicalChart
#print axioms OQ14.Packet05QuantitativePhysicalChart.quantitative_physical_chart_branches
