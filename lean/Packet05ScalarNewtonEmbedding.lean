import Packet05ComplexCorrectionWeakHessian
import NewtonL1L2

/-! Embed one actual scalar source into a single vector component so that the
existing Newton operator provides its static Hessian. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ScalarNewtonEmbedding
open MeasureTheory OQ14.Maxwell

def scalarSource (F : NewtonL2.ScalarL2) (j : Fin 3) : VectorFourier.VectorL2 :=
  VectorFourier.components.symm
    ((WithLp.equiv 2 (Fin 3 → VectorFourier.ScalarL2)).symm
      (fun k => if k = j then VectorFourier.scalarCoordinates.symm F else 0))

theorem scalarSource_coordinate (F : NewtonL2.ScalarL2) (j k : Fin 3) :
    NewtonL2.physicalCoordinate (scalarSource F j) k = if k = j then F else 0 := by
  unfold NewtonL2.physicalCoordinate
  have h : VectorFourier.coordinate k (scalarSource F j) =
      if k = j then VectorFourier.scalarCoordinates.symm F else 0 := by
    change VectorFourier.components (scalarSource F j) k = _
    simp [scalarSource]
  rw [h]
  split <;> simp

end OQ14.Packet05ScalarNewtonEmbedding
#print axioms OQ14.Packet05ScalarNewtonEmbedding.scalarSource_coordinate
