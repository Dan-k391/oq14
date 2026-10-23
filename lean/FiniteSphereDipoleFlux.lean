import StaticTrialLimit
import FinitePlaneDipole
import FiniteSpherePlaneSources

/-! The actual static coherent plane field of finitely many polarized balls is its exact dipole flux. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereDipoleFlux
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open Maxwell (conjugate)
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def dipoleFlux (k : ℝ) (p : ι → Space) (r : ι → ℝ) (P : ι → Vector)
    (q : κ → Space) (j : κ → Fin 3) (A : κ → ℂ) (z : Plane) : ℂ :=
  crossProduct (FinitePlaneDipole.dipoles p r P (MaxwellPlaneTail.planePoint z))
    (conjugate (ParityTotalFlux.incidentMagnetic k q j A (MaxwellPlaneTail.planePoint z))) 2

theorem trial_profile (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (d : ℝ)
    (hr : ∀ l, 0 < r l) (hd : 0 < d) (hh : ∀ l, d+r l ≤ |p l 2|)
    (z : Plane) (i : Fin 3) :
    NewtonSeparatedResponse.response (FiniteSpherePlaneSources.trialSource p r P) (MaxwellPlaneTail.planePoint z) i=
      FinitePlaneDipole.dipoles p r P (MaxwellPlaneTail.planePoint z) i := by
  exact FinitePlaneDipole.plane_response_eq_dipoles p r P d hr hd hh z i

theorem static_flux (k : ℝ) (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (d : ℝ)
    (hr : ∀ l, 0 < r l) (hd : 0 < d) (hh : ∀ l, d+r l ≤ |p l 2|)
    (q : κ → Space) (j : κ → Fin 3) (A : κ → ℂ) (z : Plane) :
    FiniteStaticCoherent.staticMixed k (FiniteSpherePlaneSources.trialSource p r P) q j A z=
      dipoleFlux k p r P q j A z := by
  unfold FiniteStaticCoherent.staticMixed dipoleFlux
  rw [funext (trial_profile p r P d hr hd hh z)]

end OQ14.FiniteSphereDipoleFlux
#print axioms OQ14.FiniteSphereDipoleFlux.trial_profile
#print axioms OQ14.FiniteSphereDipoleFlux.static_flux
