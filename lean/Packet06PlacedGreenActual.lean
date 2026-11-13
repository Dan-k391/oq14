import Packet06PlacedGreenMaxwell
import Packet06ProjectedGlobal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedGreenActual
open MeasureTheory Metric Maxwell DynamicSource MaterialMaxwell Packet06CyclicRotation
open Packet06PlacedGreenMaxwell Packet06ProjectedGlobal Packet06CyclicRotationMaxwell
open scoped Topology
abbrev V := VectorFourier.VectorL2

/-- The physical global projected-source field satisfies the placed equation,
with the source transformed by the exact second-order scaling factor. -/
theorem transformed_global_maxwell (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (hunit : IsUnit (Packet06MaterialSector.pencil c S z)) (f : V)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0)
    (s : ℝ) (hs : 0 < s) (a : Space) (α : ℂ) :
    weakSecond ((s : ℂ)*z)
      (fun x => 1+c.value (VectorFourier.coordinateMap (unrotate (s • (x-a)))))
      (fun x => α • rotateField (field c S J z f) (s • (x-a)))
      (fun x => α • ((s : ℂ)^2 • rotateField
        (fun y => Packet06ProjectedGreen.project f (VectorFourier.coordinateMap y)) (s • (x-a)))) := by
  have h : weakSecond z (fun x => 1+c.value (VectorFourier.coordinateMap x))
      (field c S J z f) (fun x => Packet06ProjectedGreen.project f (VectorFourier.coordinateMap x)) := by
    intro i φ
    simpa only [weakSecond, MaterialMaxwell.fieldPair, Complex.ofReal_add, Complex.ofReal_one] using
      field_global_maxwell c ha hm S J hS hJ hc z hz hunit f hf i φ
  exact placed z α s hs a _ _ _ h

#print axioms OQ14.Packet06PlacedGreenActual.transformed_global_maxwell
end OQ14.Packet06PlacedGreenActual
