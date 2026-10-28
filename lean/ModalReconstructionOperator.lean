import ModalReconstructionEnergy
import ModalAngularLinearity

noncomputable section
set_option autoImplicit false
namespace OQ14.ModalReconstructionOperator
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower
  OQ14.ModalAngularReconstruction
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

def reconstructLinear (m : C(Sphere, ComplexVectorSphere.Vector)) : VectorL2 →ₗ[ℂ] VectorL2 where
  toFun u := reconstruct u m
  map_add' u v := ModalAngularLinearity.reconstruct_add u v m
  map_smul' a u := ModalAngularLinearity.reconstruct_smul a u m

def reconstructOperator (m : C(Sphere, ComplexVectorSphere.Vector)) : VectorL2 →L[ℂ] VectorL2 :=
  (reconstructLinear m).mkContinuous (‖ContinuousMap.toLp 2 angularMeasure ℂ m‖^2)
    (fun u => ModalReconstructionEnergy.reconstruction_bound u m)

theorem reconstructOperator_actual (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    (fun x : Space => reconstructOperator m u (VectorFourier.coordinateMap x)) =ᵐ[volume]
      reconstructedField u m := ModalAngularReconstruction.reconstruct_actual u m

#print axioms OQ14.ModalReconstructionOperator.reconstructOperator_actual
end OQ14.ModalReconstructionOperator

