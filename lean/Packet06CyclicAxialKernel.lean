import Packet06CyclicAxialPencil

/-! Actual support and kernel under axial rotation and two cyclic rotations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06CyclicAxialKernel
open Metric Maxwell ModalAxialRotation Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06CyclicSectorConjugate Packet06AxialMaterialTransport Packet06CyclicAxialPencil
abbrev V := VectorFourier.VectorL2

theorem axial_support (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0) :
    ∀ x : Space, x ∉ closedBall 0 R → (coefficient θ c).value (VectorFourier.coordinateMap x)=0 := by
  intro x hx
  rw [Packet06AxialMaterialTransport.coefficient_value]
  apply hc
  simpa [mem_closedBall,dist_zero_right,(rotation (-θ)).norm_map] using hx

theorem material_support (θ : ℝ) (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s) (a : Space)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0) :
    ∀ x : Space, x ∉ closedBall 0 (R/s+‖a‖) → (material θ c s a).value (VectorFourier.coordinateMap x)=0 :=
  one_support _ _ (one_support _ _ (axial_support θ _ _ (Packet06PlacedPole.coefficient_support c R hc s hs a)))

theorem kernel_transport (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : V)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0) :
    ComplexConvolutionAnalytic.volumeBlock (material θ c s a) ((s : ℂ)*z) (R/s+‖a‖)
      (cy (cy (action θ (placed s hs a u))))=0 := by
  let L := R/s+‖a‖
  have hL : 0 ≤ L := add_nonneg (div_nonneg hR hs.le) (norm_nonneg a)
  have hp := Packet06PlacedPole.coefficient_support c R hc s hs a
  have hr := axial_support θ (placedCoefficient s a c) L hp
  have hker₀ : ComplexConvolutionAnalytic.volumeBlock (coefficient θ (placedCoefficient s a c)) ((s : ℂ)*z) L
      (action θ (placed s hs a u))=0 := by
    rw [Packet06AxialPencilTransport.volume_intertwines θ (placedCoefficient s a c) L hL hp,
      Packet06PlacedConjugacy.volume_intertwines c R hR hc s hs a z u,hu,map_zero,map_zero]
  have hker₁ := Packet06PlacedConjugacy.volume_intertwines (coefficient θ (placedCoefficient s a c)) L hL hr
    1 (by norm_num) 0 ((s : ℂ)*z) (action θ (placed s hs a u))
  have hker₂ := Packet06PlacedConjugacy.volume_intertwines (placedCoefficient 1 0 (coefficient θ (placedCoefficient s a c)))
    L hL (one_support _ L hr) 1 (by norm_num) 0 ((s : ℂ)*z) (cy (action θ (placed s hs a u)))
  simp only [Complex.ofReal_one,one_mul,div_one,norm_zero,add_zero] at hker₁ hker₂
  dsimp only [material,cy] at hker₂ ⊢
  rw [hker₂,hker₁,hker₀,map_zero,map_zero]

end OQ14.Packet06CyclicAxialKernel
#print axioms OQ14.Packet06CyclicAxialKernel.axial_support
#print axioms OQ14.Packet06CyclicAxialKernel.material_support
#print axioms OQ14.Packet06CyclicAxialKernel.kernel_transport
