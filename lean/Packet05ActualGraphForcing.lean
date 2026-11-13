import Packet05GraphPiolaCompact
import Packet05ModeCorrectionH2
import Packet05DifferentiatedSourceRegularity

/-! The actual complex Maxwell correction supplies compact graph-transformed
binary forcing with both tangential derivatives required by the iteration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualGraphForcing
open MeasureTheory Metric Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.Packet05ModeCorrectionH2 OQ14.Packet05GraphPiolaH2
  OQ14.Packet05GraphPiolaCompact OQ14.Packet05BinaryForcingTangential
  OQ14.Packet05FlatWeight OQ14.Packet05DifferentiatedSourceRegularity
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeakDivergence
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_graph_forcing (c : StaticCoefficient.Coefficient) (z : ℂ)
    (S R : ℝ) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball 0 R)
    (g : Plane → ℝ) (hg3 : ContDiff ℝ 3 g) (B : Fin 3 → ℝ)
    (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i)
    (hdi : ∀ i j, MemLp (fun x => dcoord (slopeC g i) x j) ⊤ volume)
    (hdd : ∀ i j k, MemLp (fun x => dcoord (fun y => dcoord (slopeC g i) y j) x k) ⊤ volume)
    (d : ℝ) (hd : 0 ≤ d) (i t : Fin 3) (hi : i ≠ 2) (ht : t ≠ 2) :
    ∃ P : L2Vector, ∃ Fi Ft Fit : L2Vector,
      (∀ j, ∀ᵐ x ∂volume, P j x = χ.function x *
        Packet06ComplexPotential.correction z (DynamicVolume.source c u) x j) ∧
      let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
      let Q := transformedFlux g hg P B hB
      (∀ j, CompactRepresentative (mulWeight d hd (Q j))) ∧
      (∀ j, HasWeakPartial (mulWeight d hd (Q j)) (Fi j) i) ∧
      (∀ j, HasWeakPartial (mulWeight d hd (Q j)) (Ft j) t) ∧
      (∀ j, HasWeakPartial (Fi j) (Fit j) t) := by
  classical
  have hex (j : Fin 3) := mode_correction_compact_h2 c z S R u hc χ hχ2 hχR j
  let P (j : Fin 3) := Classical.choose (hex j)
  have hp (j : Fin 3) := Classical.choose_spec (hex j)
  have hp2 (j : Fin 3) : HasH2 (P j) := by
    obtain ⟨G,H,hG,hH,_⟩ := hp j
    exact ⟨G,H,hG,hH⟩
  have hpval (j : Fin 3) : ∀ᵐ x ∂volume, P j x = χ.function x *
      Packet06ComplexPotential.correction z (DynamicVolume.source c u) x j := by
    obtain ⟨G,H,hG,hH,hval⟩ := hp j
    exact hval
  have hpc (j : Fin 3) : CompactRepresentative (P j) :=
    ⟨fun x => χ.function x * Packet06ComplexPotential.correction z (DynamicVolume.source c u) x j,
      χ.compact.mul_right, hpval j⟩
  let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
  let Q := transformedFlux g hg P B hB
  have hQ2 (j : Fin 3) : HasH2 (Q j) := graph_piola_h2 g hg3 P hp2 B hB hdi hdd j
  have hQc (j : Fin 3) : CompactRepresentative (Q j) := graph_piola_compact g hg P hpc B hB j
  have hder (j : Fin 3) := binary_h2_tangential d hd (Q j) (hQc j) (hQ2 j) i t hi ht
  let Fi (j : Fin 3) := Classical.choose (hder j)
  let Ft (j : Fin 3) := Classical.choose (Classical.choose_spec (hder j))
  let Fit (j : Fin 3) := Classical.choose (Classical.choose_spec (Classical.choose_spec (hder j)))
  refine ⟨P,Fi,Ft,Fit,hpval,?_,?_,?_,?_⟩
  · intro j
    exact weight_compact d hd (Q j) (hQc j)
  · intro j
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hder j)))).1
  · intro j
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hder j)))).2.1
  · intro j
    exact (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hder j)))).2.2

end OQ14.Packet05ActualGraphForcing
#print axioms OQ14.Packet05ActualGraphForcing.actual_graph_forcing
