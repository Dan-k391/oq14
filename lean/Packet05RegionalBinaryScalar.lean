import Packet05RegionalGraphConstitutive
import Packet05RegionalDivergenceCongruence
import Packet05ScalarDielectricFlux

/-! The actual regional dielectric scalar equation becomes the flat binary
transmission equation on a graph chart, with the correct forcing sign. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RegionalBinaryScalar
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.ConicalJunctionPhysical OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalDivergenceCongruence OQ14.Packet05RegionalGraphPiola
  OQ14.Packet05RegionalGraphConstitutive OQ14.Packet05PhysicalGraphChart
  OQ14.Packet05GraphChartMap OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphFluxExtension
  OQ14.Packet05FlatWeight OQ14.Packet05ScalarDielectricFlux OQ14.Packet05TensorCommutator
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_binary_scalar (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (V W : Set Maxwell.Space) (u : L2Scalar) (U P Q : L2Vector) (ε : Maxwell.Space → ℂ)
    (hU : ∀ i, HasWeakPartial u (U i) i) (hdiv : HasDivergenceOn V P 0)
    (hP : ∀ j, ∀ᵐ y ∂volume, y ∈ V → P j y = ε y * (U j y+Q j y))
    (hmap : ∀ x ∈ W, graphMap (liftedHeight g) x ∈ V)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i)
    (d : ℝ) (hd : 0 ≤ d)
    (hε : ∀ x ∈ W, ε (graphMap (liftedHeight g) x) = weight d x)
    (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ x ∈ W, ∀ j i, (A j i).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j i : ℂ)) :
    let C := pulledGradient g hg U B hB
    let F : L2Vector := fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)
    (∀ i, HasWeakPartial (pullback g hg.continuous u) (C i) i) ∧
      HasDivergenceOn W (fun j => flux A C d hd j-F j) 0 := by
  dsimp only
  let C := pulledGradient g hg U B hB
  let F : L2Vector := fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)
  have ht : HasDivergenceOn W (transformedFlux g hg P B hB) 0 := by
    have h := regional_graph_piola g hg V W P 0 hdiv hmap B hB
    simpa [pullback] using h
  refine ⟨graph_pullback_h1 g hg u U hU B hB, ?_⟩
  apply divergence_on_of_ae_eq W (transformedFlux g hg P B hB) (fun j => flux A C d hd j-F j) 0 ht
  intro j
  filter_upwards [regional_graph_constitutive g hg V W U P Q ε hP hmap B hB j,
    matrixField_ae A C j, mulWeight_ae d hd (matrixField A C j),
    mulWeight_ae d hd (transformedFlux g hg Q B hB j),
    Lp.coeFn_neg (mulWeight d hd (transformedFlux g hg Q B hB j)),
    Lp.coeFn_sub (flux A C d hd j) (F j)] with x hp hm hw hq hn hs hx
  change (flux A C d hd j-F j : L2Scalar) x = transformedFlux g hg P B hB j x
  rw [hs]
  simp only [Pi.sub_apply]
  change (mulWeight d hd (matrixField A C j)) x - (-mulWeight d hd (transformedFlux g hg Q B hB j) : L2Scalar) x = _
  rw [hw,hn]
  simp only [Pi.neg_apply]
  rw [hq,hp hx,hε x hx,hm]
  have he : (∑ i : Fin 3, (A j i).function x * C i x) =
      ∑ i : Fin 3, (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j i : ℂ) * C i x := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hA x hx j i]
  rw [he]
  ring

end OQ14.Packet05RegionalBinaryScalar
#print axioms OQ14.Packet05RegionalBinaryScalar.regional_binary_scalar
