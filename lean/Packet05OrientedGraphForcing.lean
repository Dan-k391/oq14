import Packet05ActualOrientedModeScalar
import Packet05GraphForcingSign
import Packet05GraphSlopeBounds

/-! The signed-chart mode correction yields exactly the compact binary
forcing and tangential derivative arrays of the regional scalar bootstrap. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05OrientedGraphForcing
open MeasureTheory OQ14.WeakCurl OQ14.DivCurlCompact OQ14.Packet05GraphPiolaH2
  OQ14.Packet05GraphPiolaCompact OQ14.Packet05BinaryForcingTangential
  OQ14.Packet05FlatWeight OQ14.Packet05DifferentiatedSourceRegularity
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeakDivergence
  OQ14.Packet05GraphForcingSign OQ14.Packet05ActualCorrectionH2 OQ14.Packet05LocalDerivative
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem oriented_graph_forcing (g : Plane → ℝ) (hg3 : ContDiff ℝ 3 g)
    (Q : L2Vector) (hQc : ∀ j, CompactRepresentative (Q j)) (hQ2 : ∀ j, HasH2 (Q j))
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i)
    (hdi : ∀ i j, MemLp (fun x => OQ14.Maxwell.dcoord (slopeC g i) x j) ⊤ volume)
    (hdd : ∀ i j k, MemLp (fun x => OQ14.Maxwell.dcoord
      (fun y => OQ14.Maxwell.dcoord (slopeC g i) y j) x k) ⊤ volume)
    (d : ℝ) (hd : 0 ≤ d) :
    let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
    let F : L2Vector := fun j => -mulWeight d hd (transformedFlux g hg Q B hB j)
    (∀ j, CompactRepresentative (F j)) ∧
    ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
      (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t) := by
  dsimp only
  classical
  let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
  let P := transformedFlux g hg Q B hB
  let F : L2Vector := fun j => -mulWeight d hd (P j)
  have hp2 (j : Fin 3) : HasH2 (P j) := graph_piola_h2 g hg3 Q hQ2 B hB hdi hdd j
  have hpc (j : Fin 3) : CompactRepresentative (P j) := graph_piola_compact g hg Q hQc B hB j
  have hfirst (i : Fin 3) (hi : i ≠ 2) (j : Fin 3) :
      ∃ D, HasWeakPartial (F j) D i := by
    obtain ⟨Di,Dt,Dit,hDi,hDt,hDit⟩ := binary_h2_tangential d hd (P j) (hpc j) (hp2 j) i i hi hi
    refine ⟨-Di,?_⟩
    simpa only [F,neg_one_smul] using weak_partial_smul (-1) _ _ i hDi
  let F1 (i : Fin 3) (j : Fin 3) := if hi : i ≠ 2 then Classical.choose (hfirst i hi j) else 0
  have hF1 (i : Fin 3) (hi : i ≠ 2) (j : Fin 3) : HasWeakPartial (F j) (F1 i j) i := by
    simpa [F1,hi] using Classical.choose_spec (hfirst i hi j)
  have hsecond (i : Fin 3) (hi : i ≠ 2) (t : Fin 3) (ht : t ≠ 2) (j : Fin 3) :
      ∃ D, HasWeakPartial (F1 i j) D t := by
    obtain ⟨Di,Dt,Dit,hDi,hDt,hDit⟩ := binary_h2_tangential d hd (P j) (hpc j) (hp2 j) i t hi ht
    have hminus : HasWeakPartial (F j) (-Di) i := by
      simpa only [F,neg_one_smul] using weak_partial_smul (-1) _ _ i hDi
    have heq : F1 i j = -Di := weak_partial_unique (F j) (F1 i j) (-Di) i (hF1 i hi j) hminus
    rw [heq]
    refine ⟨-Dit,?_⟩
    simpa only [neg_one_smul] using weak_partial_smul (-1) _ _ t hDit
  let F2 (i t : Fin 3) (j : Fin 3) :=
    if hi : i ≠ 2 then if ht : t ≠ 2 then Classical.choose (hsecond i hi t ht j) else 0 else 0
  refine ⟨?_,F1,F2,hF1,?_⟩
  · intro j
    exact OQ14.Packet05WeightedMatrixDerivative.compact_neg _ (weight_compact d hd _ (hpc j))
  · intro i hi t ht j
    simpa [F2,hi,ht] using Classical.choose_spec (hsecond i hi t ht j)

end OQ14.Packet05OrientedGraphForcing
#print axioms OQ14.Packet05OrientedGraphForcing.oriented_graph_forcing
