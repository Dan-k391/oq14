import Packet05AssembledArrayCeiling

/-! One common cutoff-array ceiling for scalar gradient and forcing. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05PairedArrayCeiling
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05QuantitativeLocalArrays Packet05PlateauGraphFlux Packet05AssembledArrayCeiling
  MaxwellCutoffCommutator

theorem paired_ceiling (θ : Test) (hθ2 : ContDiff ℝ 2 θ.function)
    (C F : L2Vector) (DC DF : Fin 3 → L2Vector) (HC HF : Fin 3 → Fin 3 → L2Vector)
    (a b c C0 C1 C2 F0 F1 F2 : ℝ) (ha : ∀ x, ‖θ.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord θ.function x i‖ ≤ b)
    (hc : ∀ i j x, ‖dcoord (derivativeCutoff θ hθ2 i).function x j‖ ≤ c)
    (hC : ∀ j, ‖C j‖ ≤ C0) (hDC : ∀ i j, ‖DC i j‖ ≤ C1)
    (hHC : ∀ i t j, ‖HC i t j‖ ≤ C2)
    (hF : ∀ j, ‖F j‖ ≤ F0) (hDF : ∀ i j, ‖DF i j‖ ≤ F1)
    (hHF : ∀ i t j, ‖HF i t j‖ ≤ F2) :
    let L := max (ceiling a b c C0 C1 C2) (ceiling a b c F0 F1 F2)
    (∀ j, ‖cutVector θ C j‖ ≤ L) ∧ (∀ j, ‖cutVector θ F j‖ ≤ L) ∧
    (∀ i j, ‖first θ C DC i j‖ ≤ L) ∧ (∀ i j, ‖first θ F DF i j‖ ≤ L) ∧
    (∀ i t j, ‖second θ hθ2 C DC HC i t j‖ ≤ L) ∧
    (∀ i t j, ‖second θ hθ2 F DF HF i t j‖ ≤ L) := by
  dsimp only
  obtain ⟨hC0,hC1,hC2⟩ := assembled_ceiling θ hθ2 C DC HC a b c C0 C1 C2 ha hb hc hC hDC hHC
  obtain ⟨hF0,hF1,hF2⟩ := assembled_ceiling θ hθ2 F DF HF a b c F0 F1 F2 ha hb hc hF hDF hHF
  exact ⟨fun j => (hC0 j).trans (le_max_left _ _),fun j => (hF0 j).trans (le_max_right _ _),
    fun i j => (hC1 i j).trans (le_max_left _ _),fun i j => (hF1 i j).trans (le_max_right _ _),
    fun i t j => (hC2 i t j).trans (le_max_left _ _),fun i t j => (hF2 i t j).trans (le_max_right _ _)⟩

end OQ14.Packet05PairedArrayCeiling
#print axioms OQ14.Packet05PairedArrayCeiling.paired_ceiling
