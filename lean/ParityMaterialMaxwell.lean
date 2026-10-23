import ParityModifiedIncident

/-! Actual complete parity material solution satisfies both dielectric Maxwell test equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityMaterialMaxwell
open MeasureTheory Maxwell MaterialMaxwell
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def magnetic (c : Coefficient) (k B : ℝ) (u : VectorL2) (H : Field) : Field :=
  ParityPlaneFields.totalMagnetic k B (DynamicVolume.source c u) H

theorem electric_identity (c : Coefficient) (k B : ℝ) (u : VectorL2) (E : Field) :
    MaterialField.total c k u (ParityModifiedIncident.electric c k B u E)=ParityMaterialField.total c k B u E := by
  funext x i
  unfold MaterialField.total ParityModifiedIncident.electric ParityMaterialField.total ParityMaterialField.scattered
  simp only [ParityPlaneFields.electric_material]
  ring

theorem magnetic_identity (c : Coefficient) (k B : ℝ) (u : VectorL2) (H : Field) :
    MaterialMaxwell.totalMagnetic c k u (ParityModifiedIncident.magnetic c k B u H)=magnetic c k B u H := by
  funext x i
  unfold MaterialMaxwell.totalMagnetic ParityModifiedIncident.magnetic magnetic ParityPlaneFields.totalMagnetic
  ring

theorem volume_testMaxwell (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (k B : ℝ) (u f : VectorL2) (E H : Field)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*E x i)
    (hsol : ParityMaterialField.block d k B u=f)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hm : TestMaxwell k (fun _ => 1) E H) :
    TestMaxwell k (dielectric c) (ParityMaterialField.total c k B u E) (magnetic c k B u H) := by
  have hloc := ParityModifiedIncident.locallyIntegrable c d k B u E H hE hH
  have hmod := ParityModifiedIncident.testMaxwell c d k B u E H hE hH hm
  have hdata := ParityModifiedIncident.weighted_datum c d k B u f E hincident hsol
  have hh := MaterialMaxwell.volume_solution_testMaxwell c k d.radius u
    (DynamicVolume.volumeBlock c k d.radius u) (ParityModifiedIncident.electric c k B u E)
    (ParityModifiedIncident.magnetic c k B u H) d.ballZero hdata rfl hloc.1 hloc.2 hmod
  rw [electric_identity,magnetic_identity] at hh
  exact hh

theorem inverse_testMaxwell (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (k B : ℝ) (hsmall : ParityReactionVolume.perturbationBound d k B < 1) (f : VectorL2) (E H : Field)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*E x i)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hm : TestMaxwell k (fun _ => 1) E H) :
    TestMaxwell k (dielectric c) (ParityMaterialField.total c k B (ParityMaterialField.solution d k B f) E)
      (magnetic c k B (ParityMaterialField.solution d k B f) H) :=
  volume_testMaxwell c d k B _ f E H hincident (ParityMaterialField.solution_equation d k B hsmall f) hE hH hm

end OQ14.ParityMaterialMaxwell
#print axioms OQ14.ParityMaterialMaxwell.electric_identity
#print axioms OQ14.ParityMaterialMaxwell.magnetic_identity
#print axioms OQ14.ParityMaterialMaxwell.volume_testMaxwell
#print axioms OQ14.ParityMaterialMaxwell.inverse_testMaxwell
