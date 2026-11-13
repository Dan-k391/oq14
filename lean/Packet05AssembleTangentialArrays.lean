import Packet05QuantitativeLocalArrays

/-! Assemble the two aligned tangential directions into the explicit global
cutoff arrays used by the physical scalar adapter. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05AssembleTangentialArrays
open Set Maxwell WeakCurl WeakPoynting WeakGreen DivCurlCompact Packet05RegionalPartial
  Packet05QuantitativeLocalArrays

def firstLocal (D0 D1 : L2Vector) : Fin 3 → L2Vector := ![D0,D1,0]
def secondLocal (H00 H01 H10 H11 : L2Vector) : Fin 3 → Fin 3 → L2Vector :=
  ![![H00,H01,0],![H10,H11,0],![0,0,0]]

theorem assemble (W : Set Space) (θ : Test) (hθ2 : ContDiff ℝ 2 θ.function)
    (hθW : tsupport θ.function ⊆ W) (C D0 D1 H00 H01 H10 H11 : L2Vector)
    (hD0 : ∀ j, HasPartialOn W (C j) (D0 j) 0)
    (hD1 : ∀ j, HasPartialOn W (C j) (D1 j) 1)
    (hH00 : ∀ j, HasPartialOn W (D0 j) (H00 j) 0)
    (hH01 : ∀ j, HasPartialOn W (D0 j) (H01 j) 1)
    (hH10 : ∀ j, HasPartialOn W (D1 j) (H10 j) 0)
    (hH11 : ∀ j, HasPartialOn W (D1 j) (H11 j) 1)
    (a b c : ℝ) (ha : ∀ x, ‖θ.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord θ.function x i‖ ≤ b)
    (hc : ∀ i j x, ‖dcoord (MaxwellCutoffCommutator.derivativeCutoff θ hθ2 i).function x j‖ ≤ c) :
    let D := firstLocal D0 D1
    let H := secondLocal H00 H01 H10 H11
    let C1 := first θ C D
    let C2 := second θ hθ2 C D H
    (∀ i, i ≠ 2 → ∀ j, HasWeakPartial
      (scaleL2 θ.function θ.regular.continuous θ.compact (C j)) (C1 i j) i) ∧
    (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (C1 i j) (C2 i t j) t) ∧
    (∀ i j, ‖C1 i j‖ ≤ a*‖D i j‖+b*‖C j‖) ∧
    (∀ i t j, ‖C2 i t j‖ ≤ a*‖H i t j‖+b*‖D i j‖+b*‖D t j‖+c*‖C j‖) := by
  dsimp only
  have hD : ∀ i, i ≠ 2 → ∀ j, HasPartialOn W (C j) (firstLocal D0 D1 i j) i := by
    intro i hi j
    fin_cases i
    · exact hD0 j
    · exact hD1 j
    · exact (hi rfl).elim
  have hH : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j,
      HasPartialOn W (firstLocal D0 D1 i j) (secondLocal H00 H01 H10 H11 i t j) t := by
    intro i hi t ht j
    fin_cases i <;> fin_cases t
    · exact hH00 j
    · exact hH01 j
    · exact (ht rfl).elim
    · exact hH10 j
    · exact hH11 j
    · exact (ht rfl).elim
    · exact (hi rfl).elim
    · exact (hi rfl).elim
    · exact (hi rfl).elim
  obtain ⟨hfirst,hsecond⟩ := local_arrays W θ hθ2 hθW C (firstLocal D0 D1)
    (secondLocal H00 H01 H10 H11) hD hH
  exact ⟨hfirst,hsecond,fun i j => first_norm θ C (firstLocal D0 D1) i j a b ha hb,
    fun i t j => second_norm θ hθ2 C (firstLocal D0 D1) (secondLocal H00 H01 H10 H11)
      i t j a b c ha hb hc⟩

end OQ14.Packet05AssembleTangentialArrays
#print axioms OQ14.Packet05AssembleTangentialArrays.assemble
