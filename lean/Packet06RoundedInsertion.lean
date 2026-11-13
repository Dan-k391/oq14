import Packet06CertifiedInsertion
import Packet06ConeUnionSymmetry

/-! Actual fixed-contrast geometric rounding retains the hypotheses of the
proved material perturbation theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06RoundedInsertion
open Filter Set Metric MeasureTheory Packet06MaterialSymmetry Packet06ContrastInsertion
open StaticCoefficient (Coefficient)
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def sharp (base : Coefficient) (η : ℝ) (hη : 0 ≤ η) : Coefficient :=
  addScaled base (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep) η hη

def rounded (ha0 : ∀ i, 0 < a i) (base : Coefficient) (η : ℝ) (hη : 0 ≤ η) (j : ℕ) : Coefficient :=
  addScaled base (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 j) η hη

theorem admissible (ha0 : ∀ i, 0 < a i) (base : Coefficient) (η : ℝ) (hη : 0 ≤ η)
    (hbase : ∀ x : Space, x ∉ closedBall 0 1 → base.value (VectorFourier.coordinateMap x) = 0)
    (hax : Axial base) (hmer : Meridional base)
    (haxis : Packet06ConeUnionSymmetry.OnAxis center)
    (hinside : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) 1) :
    let c := rounded p a center B hB hcontrast ha hsep ha0 base η hη
    let c₀ := sharp p a center B hB hcontrast ha hsep base η hη
    (∀ j, (c j).bound ≤ base.bound+η*B) ∧ c₀.bound ≤ base.bound+η*B ∧
    (∀ᵐ x : StaticCoefficient.Space, Tendsto (fun j => (c j).value x) atTop (𝓝 (c₀.value x))) ∧
    (∀ (j : ℕ) (x : Space), x ∉ closedBall 0 1 → (c j).value (VectorFourier.coordinateMap x) = 0) ∧
    (∀ x : Space, x ∉ closedBall 0 1 → c₀.value (VectorFourier.coordinateMap x) = 0) ∧
    (∀ j, Axial (c j)) ∧ (∀ j, Meridional (c j)) ∧ Axial c₀ ∧ Meridional c₀ := by
  dsimp only
  refine ⟨fun _ => le_rfl,le_rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · filter_upwards [CommonBinaryRounding.coefficient_eventually_eq p a center B hB hcontrast ha hsep ha0] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hx] with j hj
    change base.value x+η*(ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep).value x =
      base.value x+η*(CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 j).value x
    rw [hj]
  · intro j
    exact support base _ η hη 1 hbase
      (CommonBinaryRounding.coefficient_support p a center B hB hcontrast ha hsep ha0 j 1 hinside)
  · exact support base _ η hη 1 hbase
      (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep 1 hinside)
  · intro j
    exact axial base _ η hη hax
      (Packet06ConeUnionSymmetry.rounded_axial p a center B hB hcontrast ha hsep ha0 haxis j)
  · intro j
    exact meridional base _ η hη hmer
      (Packet06ConeUnionSymmetry.rounded_meridional p a center B hB hcontrast ha hsep ha0 haxis j)
  · exact axial base _ η hη hax
      (Packet06ConeUnionSymmetry.literal_axial p a center B hB hcontrast ha hsep haxis)
  · exact meridional base _ η hη hmer
      (Packet06ConeUnionSymmetry.literal_meridional p a center B hB hcontrast ha hsep haxis)

end OQ14.Packet06RoundedInsertion
#print axioms OQ14.Packet06RoundedInsertion.admissible
