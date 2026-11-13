import Packet05QuantitativePhysicalChart
import Packet05PhaseCoverLocalBound

/-! The two chart half-spaces are dense up to their shared interface,
including after the actual physical chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05PhysicalHalfspaceClosure
open Set Maxwell Packet05ChartBasis Packet05ChartLinearEquiv Packet05GraphChartMap
  Packet05GraphChartHomeomorph Packet05PhysicalGraphChart Packet05PhysicalChartBranches
open scoped Topology
abbrev Plane := ConicalSmoothJunction.Plane

theorem flat_negative_closure : {x : Space | x 2 ≤ 0} ⊆ closure {x : Space | x 2 < 0} := by
  let P := EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)
  have hs : Function.Surjective P := by
    intro t
    exact ⟨EuclideanSpace.single 2 t, by simp [P]⟩
  have ho : IsOpenMap P := P.isOpenMap hs
  have h := ho.preimage_closure_subset_closure_preimage (s := Set.Iio (0 : ℝ))
  simpa [P,closure_Iio] using h

theorem physical_negative_closure (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (T : Set Space) (hT : IsOpen T) :
    physicalFlatMap up i g ⁻¹' (T ∩ {x | x 2 ≤ 0}) ⊆
      closure (physicalFlatMap up i g ⁻¹' (T ∩ {x | x 2 < 0})) := by
  let q := physicalFlatMap up i g
  have hqopen : IsOpenMap q := by
    let H := graphHomeomorph (liftedHeight g) (liftedHeight_continuous g hg.continuous)
      (liftedHeight_normal_invariant g)
    change IsOpenMap (fun y => H.symm (orientedHomeomorph up i y))
    exact H.symm.isOpenMap.comp (orientedHomeomorph up i).isOpenMap
  intro x hx
  have hflat : q x ∈ closure (T ∩ {x : Space | x 2 < 0}) :=
    by simpa [inter_comm] using hT.closure_inter ⟨flat_negative_closure hx.2,hx.1⟩
  exact hqopen.preimage_closure_subset_closure_preimage hflat

end OQ14.Packet05PhysicalHalfspaceClosure
#print axioms OQ14.Packet05PhysicalHalfspaceClosure.flat_negative_closure
#print axioms OQ14.Packet05PhysicalHalfspaceClosure.physical_negative_closure
