import ComplexMagneticLocal
import AngularPower
import Mathlib.MeasureTheory.Integral.Prod

/-! Product-measure consequences for actual magnetic sphere integrals.
The joint integrability hypothesis is a separate analytic obligation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet02Surface
open MeasureTheory OQ14.Maxwell OQ14.AngularPower
open OQ14.WeakCurl (next previous)

def entry (z : ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ) (j l : Fin 3)
    (p : Sphere × Space) : ℂ :=
  ρ l p.2 * ComplexGreenKernel.phiGradient z (r • (p.1 : Space) - p.2) j

theorem entries_ae_of_joint (z : ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ)
    (h : ∀ j l, Integrable (entry z ρ r j l) (angularMeasure.prod volume)) :
    ∀ᵐ (ω : Sphere) ∂angularMeasure, ∀ j l,
      Integrable (fun y => ρ l y * ComplexGreenKernel.phiGradient z
        (r • (ω : Space) - y) j) volume := by
  have h' : ∀ j l, ∀ᵐ (ω : Sphere) ∂angularMeasure,
      Integrable (fun y => entry z ρ r j l (ω,y)) volume :=
    fun j l => (h j l).prod_right_ae
  exact ae_all_iff.mpr (fun j => ae_all_iff.mpr (h' j))

theorem response_integrable_of_joint (z : ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ)
    (j l : Fin 3) (h : Integrable (entry z ρ r j l) (angularMeasure.prod volume)) :
    Integrable (fun ω : Sphere => KernelConvolution.response
      (fun x => ComplexGreenKernel.phiGradient z x j) (ρ l) (r • (ω : Space)))
      angularMeasure := by
  simpa only [entry, KernelConvolution.response] using h.integral_prod_left

theorem magnetic_integrable_of_joint (z : ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ)
    (h : ∀ j l, Integrable (entry z ρ r j l) (angularMeasure.prod volume))
    (i : Fin 3) :
    Integrable (fun ω : Sphere => ComplexMagneticLocal.magnetic z ρ (r • (ω : Space)) i)
      angularMeasure := by
  exact ((response_integrable_of_joint z ρ r (next i) (previous i) (h _ _)).sub
    (response_integrable_of_joint z ρ r (previous i) (next i) (h _ _))).const_mul _

end OQ14.Packet02Surface
#print axioms OQ14.Packet02Surface.entries_ae_of_joint
#print axioms OQ14.Packet02Surface.magnetic_integrable_of_joint

#print axioms OQ14.Packet02Surface.response_integrable_of_joint
