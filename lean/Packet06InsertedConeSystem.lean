import Packet06ComplexConeSystem
import Packet06ActualConeBranch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06InsertedConeSystem
open Metric OQ14.Maxwell
abbrev Space := Maxwell.Space
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → ConicalStaticVolume.Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

omit [DecidableEq ι] in
theorem actual_local_match (n : ℝ) (hn : 1 < n) (i : ι) (hcontrast_i : (p i).contrast = n^2)
    (η : ℝ) (hη : 0 ≤ η) (q : ConicalStaticVolume.Data)
    (hqcontrast : q.contrast = η) (hqthreshold : q.threshold = (p i).threshold)
    (b : ℝ) (hb : b ≤ a i) (hsphere : ∀ y ∈ ball (0 : Space) b, ‖y+center i‖ < 1)
    (y : Space) (hy : y ∈ ball (0 : Space) b) :
    1 + (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn)
      (ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep) η hη).value
      (VectorFourier.coordinateMap (y+center i)) = n^2 * ConicalLocalGauss.epsilon q y := by
  have hy' : ‖(y+center i)-center i‖ ≤ a i := by
    have hyb : ‖y‖ < b := by simpa using hy
    simpa using hyb.le.trans hb
  have h := Packet06ActualConeBranch.local_dielectric_match p a center B hB hcontrast ha hsep n hn i hcontrast_i η hη
    (y+center i) hy' (hsphere y hy)
  simpa [ConicalLocalGauss.epsilon, hqcontrast, hqthreshold] using h
#print axioms OQ14.Packet06InsertedConeSystem.actual_local_match
end OQ14.Packet06InsertedConeSystem
