import DensityWeak
import ParityDensityMaxwell
import MaterialMaxwell

/-! Actual weak Maxwell equations for literal parity density pairs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityDensityWeak
open MeasureTheory Maxwell MaterialMaxwell DynamicSource MagneticResponse
open WeakCurl (next previous)
open SphereReactionKernel (reaction entryBound)
open SphereMagneticParity (magneticReaction)

theorem testMaxwell (e : Bool) (k : ℝ) (ρ : PlaneSourceKernel.Source)
    (hρ : ∀ j, Integrable (ρ j)) :
    TestMaxwell k (fun _ => 1) (ParityPlaneFields.electric e k ρ) (ParityPlaneFields.magnetic e k ρ) := by
  intro i f
  have he := DensityWeak.curl_pairing (fun x y i j => reaction e k x y i j)
    (fun x y i j => magneticReaction e k x y i j) ρ hρ
    (fun x y i j => SphereParityMaxwell.electric_differentiable e k x y i j)
    (fun x i j => SphereParityDifferential.electric_differential_source_continuous e k x i j)
    (2*entryBound k*|k|) (fun x y i j => FiniteSphereIncident.reaction_derivative_bound e k x y i j)
    (fun x i j => ParityPlaneFields.electric_integrand e k ρ hρ x i j) (Complex.I*(k : ℂ))
    (fun x y i j => SphereMagneticParity.curl_reaction e k x y i j) f.val (f.val.smooth 1) f.property
  have hh := DensityWeak.curl_pairing (fun x y i j => magneticReaction e k x y i j)
    (fun x y i j => reaction e k x y i j) ρ hρ
    (fun x y i j => SphereParityMaxwell.magnetic_differentiable e k x y i j)
    (fun x i j => SphereParityDifferential.magnetic_differential_source_continuous e k x i j)
    (3*entryBound k*|k|) (fun x y i j => SphereParityDifferential.magnetic_differential_bound e k x y i j)
    (fun x i j => ParityPlaneFields.magnetic_integrand e k ρ hρ x i j) (-(Complex.I*(k : ℂ)))
    (fun x y i j => SphereParityMaxwell.curl_magnetic e k x y i j) f.val (f.val.smooth 1) f.property
  have hp (F : Field) : weakCurlPairing F f.val i=curlPair (fieldPair F) i f := by
    fin_cases i <;> simp [weakCurlPairing,curlPair,fieldPair,next,previous,testPartial,GradientProjection.pderivative_apply]
  have he' := congrFun he i
  have hh' := congrFun hh i
  change weakCurlPairing (ParityPlaneFields.electric e k ρ) f.val i=_ at he'
  change weakCurlPairing (ParityPlaneFields.magnetic e k ρ) f.val i=_ at hh'
  rw [hp] at he' hh'
  exact ⟨he',by simpa only [Complex.ofReal_one,one_mul] using hh'⟩

end OQ14.ParityDensityWeak
#print axioms OQ14.ParityDensityWeak.testMaxwell
