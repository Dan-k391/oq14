import Packet06PlacedProjection
import DilationReciprocity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PlacedGreenPairing
open Maxwell KernelReciprocity ComplexVolumeReciprocity Packet06PlacedEquivalence
abbrev V := VectorFourier.VectorL2

/-- The actual normalized placement preserves the physical complex-bilinear
source/mode pairing exactly, including the dilation Jacobian. -/
theorem placed_pair (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (u v : V) :
    vectorPair (placed s hs a u) (placed s hs a v) = vectorPair u v := by
  rw [placed_apply,placed_apply]
  dsimp only [Packet06PlacedKernel.placedUnknown]
  rw [Packet06TranslationL2.vectorPair_invariant,vectorPair_smul_left,
    vectorPair_comm,vectorPair_smul_left,vectorPair_comm,
    DilationReciprocity.vectorPair_dilate s hs,Packet06CyclicL2.vectorPair_invariant]
  have hsq : (Real.sqrt s : ℂ)*(Real.sqrt s : ℂ) = (s : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hs.le
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [← mul_assoc, ← mul_assoc, hsq,mul_inv_cancel₀ hs0,one_mul]

#print axioms OQ14.Packet06PlacedGreenPairing.placed_pair
end OQ14.Packet06PlacedGreenPairing
