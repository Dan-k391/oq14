import Packet05ActualGraphForcing

/-! Sign conversion for the scalar iteration: Gauss gives div ε(∇u+W)=0,
so the forcing in div(flux−F)=0 is the negative weighted correction. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphForcingSign
open OQ14.WeakCurl OQ14.DivCurlCompact OQ14.Packet05FlatWeight
  OQ14.Packet05ActualCorrectionH2 OQ14.Packet05WeightedMatrixDerivative

theorem negative_binary_forcing (d : ℝ) (hd : 0 ≤ d) (Q Di Dt Dit : L2Vector)
    (i t : Fin 3)
    (hc : ∀ j, CompactRepresentative (mulWeight d hd (Q j)))
    (hi : ∀ j, HasWeakPartial (mulWeight d hd (Q j)) (Di j) i)
    (ht : ∀ j, HasWeakPartial (mulWeight d hd (Q j)) (Dt j) t)
    (hit : ∀ j, HasWeakPartial (Di j) (Dit j) t) :
    (∀ j, CompactRepresentative (-(mulWeight d hd (Q j)))) ∧
    (∀ j, HasWeakPartial (-(mulWeight d hd (Q j))) (-Di j) i) ∧
    (∀ j, HasWeakPartial (-(mulWeight d hd (Q j))) (-Dt j) t) ∧
    (∀ j, HasWeakPartial (-Di j) (-Dit j) t) := by
  refine ⟨fun j => compact_neg _ (hc j), ?_, ?_, ?_⟩
  · intro j
    simpa only [neg_one_smul] using weak_partial_smul (-1) _ _ i (hi j)
  · intro j
    simpa only [neg_one_smul] using weak_partial_smul (-1) _ _ t (ht j)
  · intro j
    simpa only [neg_one_smul] using weak_partial_smul (-1) _ _ t (hit j)

end OQ14.Packet05GraphForcingSign
#print axioms OQ14.Packet05GraphForcingSign.negative_binary_forcing
