import FiniteBallWeak
import ParityTotalFlux

/-! Actual finite-ball material fields have a unique continuous strip representative and plane trace. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteBallPlaneFields
open MeasureTheory Metric Set MaterialMaxwell
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype ι] in
theorem representative (p : ι → Space) (r : ι → ℝ) (χ R d k B : ℝ) (hχ : 0 ≤ χ)
    (hd : 0 < d) (hs : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p r χ hχ))
    (hR : hs.radius=R) (hh : ∀ l, d+r l ≤ |p l 2|) (u : VectorFourier.VectorL2)
    (q : κ → Space) (j : κ → Fin 3) (A : κ → ℂ) (i : Fin 3) :
    let c := FiniteSphereStatic.coefficient p r χ hχ
    let S := DynamicVolume.source c u
    let E := ParityTotalFlux.incidentElectric k q j A
    let H := ParityTotalFlux.incidentMagnetic k q j A
    ContinuousOn (fun x => ParityPlaneFields.totalElectric k B S E x i) (NewtonSeparatedResponse.strip d) ∧
    ContinuousOn (fun x => ParityPlaneFields.totalMagnetic k B S H x i) (NewtonSeparatedResponse.strip d) ∧
    (∀ᵐ x : Space, x ∈ NewtonSeparatedResponse.strip d →
      ParityMaterialField.total c k B u E x i=ParityPlaneFields.totalElectric k B S E x i) ∧
    (∀ g : Space → ℂ, ContinuousOn g (NewtonSeparatedResponse.strip d) →
      (∀ᵐ x : Space, x ∈ NewtonSeparatedResponse.strip d → ParityMaterialField.total c k B u E x i=g x) →
      ∀ z : PlaneInverseCube.Plane, g (MaxwellPlaneTail.planePoint z)=
        ParityPlaneFields.totalElectric k B S E (MaxwellPlaneTail.planePoint z) i) := by
  dsimp only
  have hc (x : Space) (hx : x ∉ closedBall 0 R) :
      (FiniteSphereStatic.coefficient p r χ hχ).value (VectorFourier.coordinateMap x)=0 := by
    apply hs.ballZero x
    simpa only [hR] using hx
  have hS := DynamicVolume.source_integrable _ u R hc
  have hgap := StaticPlaneInclusions.material_gap p r χ d hχ hh u
  have hE (n : Fin 3) : Continuous (fun x => ParityTotalFlux.incidentElectric k q j A x n) :=
    continuous_iff_continuousAt.mpr (fun x => (FiniteSphereMaxwell.electric_differentiable k (fun _ => true) q j A x n).continuousAt)
  have hH (n : Fin 3) : Continuous (fun x => ParityTotalFlux.incidentMagnetic k q j A x n) :=
    continuous_iff_continuousAt.mpr (fun x => (FiniteSphereMaxwell.magnetic_differentiable k (fun _ => true) q j A x n).continuousAt)
  have he := ParityPlaneFields.total_electric_continuousOn k B d hd _ hS hgap _ hE i
  have ha := ParityPlaneFields.material_total_ae_strip _ k B R d hd u (ParityTotalFlux.incidentElectric k q j A) hc hgap i
  refine ⟨he,ParityPlaneFields.total_magnetic_continuousOn k B d hd _ hS hgap _ hH i,ha,?_⟩
  intro g hg hag z
  have heq : ∀ᵐ x : Space, x ∈ NewtonSeparatedResponse.strip d →
      g x=ParityPlaneFields.totalElectric k B (DynamicVolume.source (FiniteSphereStatic.coefficient p r χ hχ) u)
        (ParityTotalFlux.incidentElectric k q j A) x i := by
    filter_upwards [ha,hag] with x hx hy hstrip
    exact (hy hstrip).symm.trans (hx hstrip)
  exact NewtonSeparatedResponse.representative_unique d g _ hg he heq (by
    simp [NewtonSeparatedResponse.strip,MaxwellPlaneTail.planePoint,hd])

omit [Fintype ι] in
theorem flux_trace (k B : ℝ) (S : PlaneSourceKernel.Source) (q : κ → Space) (j : κ → Fin 3)
    (A : κ → ℂ) (z : PlaneInverseCube.Plane) :
    ParityTotalFlux.totalFlux k B S q j A z=
      crossProduct (ParityPlaneFields.totalElectric k B S (ParityTotalFlux.incidentElectric k q j A) (MaxwellPlaneTail.planePoint z))
        (Maxwell.conjugate (ParityPlaneFields.totalMagnetic k B S (ParityTotalFlux.incidentMagnetic k q j A) (MaxwellPlaneTail.planePoint z))) 2 := rfl

end OQ14.FiniteBallPlaneFields
#print axioms OQ14.FiniteBallPlaneFields.representative
#print axioms OQ14.FiniteBallPlaneFields.flux_trace
