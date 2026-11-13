import Packet05OrientedGraphForcing
import Packet05ScalarResidualBound

/-! Exact tangential forcing derivatives and bounds from the true Piola H² arrays. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05QuantitativeBinaryForcing
open OQ14.WeakCurl OQ14.WeakPoynting OQ14.DivCurlCompact OQ14.Packet05FlatWeight
  OQ14.Packet05WeakFourier OQ14.Packet05DirectionalWeightDerivative
  OQ14.Packet05GraphPiolaH2 OQ14.Packet05ActualCorrectionH2
  OQ14.Packet05WeightedMatrixDerivative

theorem binary_forcing_arrays (d : ℝ) (hd : 0 ≤ d) (P : L2Vector)
    (G : Fin 3 → L2Vector) (H : Fin 3 → Fin 3 → L2Vector)
    (hP : ∀ j, CompactRepresentative (P j))
    (hG : ∀ i j, HasWeakPartial (P j) (G i j) i)
    (hH : ∀ i t j, HasWeakPartial (G i j) (H i t j) t) :
    let F : L2Vector := fun j => -mulWeight d hd (P j)
    let F1 : Fin 3 → L2Vector := fun i j => -mulWeight d hd (G i j)
    let F2 : Fin 3 → Fin 3 → L2Vector := fun i t j => -mulWeight d hd (H i t j)
    (∀ j, CompactRepresentative (F j)) ∧
    (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i) ∧
    (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t) ∧
    (∀ j, ‖F j‖ ≤ (1+d)*‖P j‖) ∧
    (∀ i j, ‖F1 i j‖ ≤ (1+d)*‖G i j‖) ∧
    (∀ i t j, ‖F2 i t j‖ ≤ (1+d)*‖H i t j‖) := by
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro j
    exact compact_neg _ (OQ14.Packet05DifferentiatedSourceRegularity.weight_compact d hd _ (hP j))
  · intro i hi j
    have h := directional_weighted_tangential_partial d hd (P j) (G i j) (hP j) i hi (hG i j)
    simpa only [neg_one_smul] using weak_partial_smul (-1) _ _ i h
  · intro i hi t ht j
    have hc := weak_partial_compact (hP j) i (hG i j)
    have h := directional_weighted_tangential_partial d hd (G i j) (H i t j) hc t ht (hH i t j)
    simpa only [neg_one_smul] using weak_partial_smul (-1) _ _ t h
  · intro j
    simpa only [norm_neg] using OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd (P j)
  · intro i j
    simpa only [norm_neg] using OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd (G i j)
  · intro i t j
    simpa only [norm_neg] using OQ14.Packet05ScalarResidualBound.weight_norm_bound d hd (H i t j)

end OQ14.Packet05QuantitativeBinaryForcing
#print axioms OQ14.Packet05QuantitativeBinaryForcing.binary_forcing_arrays
