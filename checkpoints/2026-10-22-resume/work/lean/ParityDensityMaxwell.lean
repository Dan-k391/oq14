import DensityCurl
import SphereParityDifferential
import ParityPlaneFields

/-! Genuine global Maxwell equations for actual integrable parity density fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityDensityMaxwell
open MeasureTheory Metric PlaneSourceKernel
open SphereReactionKernel (reaction entryBound)
open SphereMagneticParity (magneticReaction)
open Maxwell (curl MaxwellAt)
abbrev Space := FourierL2.Space

theorem electric_differentiable (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (i : Fin 3) : DifferentiableAt ℝ (fun z => ParityPlaneFields.electric e k ρ z i) x :=
  DensityCurl.differentiable (fun x y i j => reaction e k x y i j) ρ hρ
    (fun x y i j => SphereParityMaxwell.electric_differentiable e k x y i j)
    (fun x i j => SphereParityDifferential.electric_differential_source_continuous e k x i j)
    (2*entryBound k*|k|) (fun x y i j => FiniteSphereIncident.reaction_derivative_bound e k x y i j)
    (fun x i j => ParityPlaneFields.electric_integrand e k ρ hρ x i j) x i

theorem magnetic_differentiable (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (i : Fin 3) : DifferentiableAt ℝ (fun z => ParityPlaneFields.magnetic e k ρ z i) x :=
  DensityCurl.differentiable (fun x y i j => magneticReaction e k x y i j) ρ hρ
    (fun x y i j => SphereParityMaxwell.magnetic_differentiable e k x y i j)
    (fun x i j => SphereParityDifferential.magnetic_differential_source_continuous e k x i j)
    (3*entryBound k*|k|) (fun x y i j => SphereParityDifferential.magnetic_differential_bound e k x y i j)
    (fun x i j => ParityPlaneFields.magnetic_integrand e k ρ hρ x i j) x i

theorem curl_electric (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (i : Fin 3) :
    curl (ParityPlaneFields.electric e k ρ) x i=(Complex.I*(k : ℂ))*ParityPlaneFields.magnetic e k ρ x i :=
  DensityCurl.curl_integral (fun x y i j => reaction e k x y i j)
    (fun x y i j => magneticReaction e k x y i j) ρ hρ
    (fun x y i j => SphereParityMaxwell.electric_differentiable e k x y i j)
    (fun x i j => SphereParityDifferential.electric_differential_source_continuous e k x i j)
    (2*entryBound k*|k|) (fun x y i j => FiniteSphereIncident.reaction_derivative_bound e k x y i j)
    (fun x i j => ParityPlaneFields.electric_integrand e k ρ hρ x i j) (Complex.I*(k : ℂ))
    (fun x y i j => SphereMagneticParity.curl_reaction e k x y i j) x i

theorem curl_magnetic (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j))
    (x : Space) (i : Fin 3) :
    curl (ParityPlaneFields.magnetic e k ρ) x i=-(Complex.I*(k : ℂ))*ParityPlaneFields.electric e k ρ x i :=
  DensityCurl.curl_integral (fun x y i j => magneticReaction e k x y i j)
    (fun x y i j => reaction e k x y i j) ρ hρ
    (fun x y i j => SphereParityMaxwell.magnetic_differentiable e k x y i j)
    (fun x i j => SphereParityDifferential.magnetic_differential_source_continuous e k x i j)
    (3*entryBound k*|k|) (fun x y i j => SphereParityDifferential.magnetic_differential_bound e k x y i j)
    (fun x i j => ParityPlaneFields.magnetic_integrand e k ρ hρ x i j) (-(Complex.I*(k : ℂ)))
    (fun x y i j => SphereParityMaxwell.curl_magnetic e k x y i j) x i

theorem maxwell (e : Bool) (k : ℝ) (ρ : Source) (hρ : ∀ j, Integrable (ρ j)) (x : Space) :
    MaxwellAt k 1 1 (ParityPlaneFields.electric e k ρ) (ParityPlaneFields.magnetic e k ρ) x := by
  constructor
  · funext i
    simpa only [Complex.ofReal_one,mul_one] using curl_electric e k ρ hρ x i
  · funext i
    simpa only [Complex.ofReal_one,mul_one,neg_mul] using curl_magnetic e k ρ hρ x i

theorem material_curl (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (e : Bool) (k : ℝ) (u : VectorFourier.VectorL2) (x : Space) (i : Fin 3) :
    curl (ParityMaterialField.reaction c e k u) x i=
      (Complex.I*(k : ℂ))*ParityPlaneFields.magnetic e k (DynamicVolume.source c u) x i :=
  curl_electric e k (DynamicVolume.source c u) (DynamicVolume.source_integrable c u d.radius d.ballZero) x i

theorem material_maxwell (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (e : Bool) (k : ℝ) (u : VectorFourier.VectorL2) (x : Space) :
    MaxwellAt k 1 1 (ParityMaterialField.reaction c e k u)
      (ParityPlaneFields.magnetic e k (DynamicVolume.source c u)) x :=
  maxwell e k (DynamicVolume.source c u) (DynamicVolume.source_integrable c u d.radius d.ballZero) x

end OQ14.ParityDensityMaxwell
#print axioms OQ14.ParityDensityMaxwell.electric_differentiable
#print axioms OQ14.ParityDensityMaxwell.magnetic_differentiable
#print axioms OQ14.ParityDensityMaxwell.curl_electric
#print axioms OQ14.ParityDensityMaxwell.curl_magnetic
#print axioms OQ14.ParityDensityMaxwell.maxwell
#print axioms OQ14.ParityDensityMaxwell.material_curl
#print axioms OQ14.ParityDensityMaxwell.material_maxwell
