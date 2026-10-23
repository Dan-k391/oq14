import SourceParityFlux
import ParityPlaneBounds
import ParityIncidentFlux
import SourceHerglotzFinite

/-! Exact complete parity material plane flux for literal electric-wall finite illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityTotalFlux
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open Maxwell (conjugate)
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

def incidentElectric (k : ℝ) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) : Maxwell.Field :=
  FiniteHerglotzFlux.electric k (fun _ => true) p j A

def incidentMagnetic (k : ℝ) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) : Maxwell.Field :=
  FiniteHerglotzFlux.magnetic k (fun _ => true) p j A

def totalFlux (k B : ℝ) (ρ : Source) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) : ℂ :=
  crossProduct (ParityPlaneFields.totalElectric k B ρ (incidentElectric k p j A) (MaxwellPlaneTail.planePoint q))
    (conjugate (ParityPlaneFields.totalMagnetic k B ρ (incidentMagnetic k p j A) (MaxwellPlaneTail.planePoint q))) 2

def freeFlux (k : ℝ) (ρ : Source) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) : ℂ :=
  crossProduct (fun i => incidentElectric k p j A (MaxwellPlaneTail.planePoint q) i+
      ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q) i)
    (conjugate (fun i => incidentMagnetic k p j A (MaxwellPlaneTail.planePoint q) i+
      MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) i)) 2

def remainder (k B : ℝ) (ρ : Source) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) : ℂ :=
  conj (((B^2-1 : ℝ) : ℂ))*SourceParityFlux.electric true k ρ ρ q+
    (((B⁻¹^2-1 : ℝ) : ℂ))*ParityIncidentFlux.flux false k ρ (fun _ => true) p j A q+
    (((B⁻¹^2-1 : ℝ) : ℂ))*SourceParityFlux.magnetic false k ρ ρ q+
    (((B⁻¹^2-1 : ℝ) : ℂ))*conj (((B^2-1 : ℝ) : ℂ))*ParityPlaneBounds.flux false true k ρ ρ q

theorem free_identity (k : ℝ) (ρ : Source) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) :
    freeFlux k ρ p j A q=SourceHerglotzFinite.electricMixed k ρ (fun _ => true) p j A q+
      MaxwellPlaneL1.flux k ρ ρ q := by
  have hzero (i : Fin 3) (hi : i ≠ 2) : incidentElectric k p j A (MaxwellPlaneTail.planePoint q) i=0 :=
    ParityIncidentFlux.incident_electric_zero k p j A _ (by rfl) i hi
  unfold freeFlux SourceHerglotzFinite.electricMixed MaxwellPlaneL1.flux MaxwellPlaneTail.bilinearFlux
  simp [cross_apply,conjugate,incidentMagnetic]
  rw [hzero 0 (by decide),hzero 1 (by decide)]
  simp only [zero_add,map_add]
  ring

theorem total_identity (k B : ℝ) (ρ : Source) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ) (q : Plane) :
    totalFlux k B ρ p j A q=freeFlux k ρ p j A q+remainder k B ρ p j A q := by
  have hi (i : Fin 3) (h : i ≠ 2) : incidentElectric k p j A (MaxwellPlaneTail.planePoint q) i=0 :=
    ParityIncidentFlux.incident_electric_zero k p j A _ (by rfl) i h
  have he (i : Fin 3) (h : i ≠ 2) : ParityPlaneFields.electric true k ρ (MaxwellPlaneTail.planePoint q) i=0 :=
    ParityPlaneFields.electric_true_zero k ρ _ (by rfl) i h
  have hh (i : Fin 3) (h : i ≠ 2) : ParityPlaneFields.magnetic false k ρ (MaxwellPlaneTail.planePoint q) i=0 :=
    ParityPlaneFields.magnetic_false_zero k ρ _ (by rfl) i h
  unfold totalFlux ParityPlaneFields.totalElectric ParityPlaneFields.totalMagnetic freeFlux remainder
    SourceParityFlux.electric SourceParityFlux.magnetic ParityPlaneBounds.flux ParityIncidentFlux.flux
  simp [cross_apply,conjugate,incidentMagnetic]
  rw [hi 0 (by decide),hi 1 (by decide),he 0 (by decide),he 1 (by decide),hh 0 (by decide),hh 1 (by decide)]
  simp only [mul_zero,zero_add,add_zero,map_add,map_mul,map_zero,Complex.star_def]
  ring

end OQ14.ParityTotalFlux
#print axioms OQ14.ParityTotalFlux.free_identity
#print axioms OQ14.ParityTotalFlux.total_identity
