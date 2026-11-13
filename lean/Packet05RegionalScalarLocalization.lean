import Packet05ScalarFluxAlgebra
import Packet05LocalPartialProduct
import Packet05DifferentiatedSourceRegularity
import Packet05ScalarSquareCutoff

/-! Localize a regional scalar transmission equation into compact global
fields, preserving its divergence-form structure and recording the outer
cutoff source exactly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RegionalScalarLocalization
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.Packet05LocalPartialProduct OQ14.Packet05RegionalDivergence OQ14.Packet05RegionalFluxCutoff
  OQ14.Packet05FlatWeight OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarSquareCutoff OQ14.Packet05ScalarCutoffTesting
  OQ14.Packet05ScalarFluxAlgebra OQ14.Packet05WeightedMatrixDerivative OQ14.Packet05DifferentiatedSourceRegularity
open scoped Topology

def cutoffCorrection (ζ : RealTest Set.univ) (v : L2Scalar) : L2Vector :=
  fun j => cutoffGradient ζ v j

def localizedGradient (ζ : RealTest Set.univ) (v : L2Scalar) (G : L2Vector) : L2Vector :=
  fun j => cutVector ζ G j + cutoffCorrection ζ v j

def localizedForcing (ζ : RealTest Set.univ) (A : Fin 3 → Fin 3 → Test)
    (v : L2Scalar) (F : L2Vector) (d : ℝ) (hd : 0 ≤ d) : L2Vector :=
  fun j => cutVector ζ F j + flux A (cutoffCorrection ζ v) d hd j

theorem localized_scalar_flux_identity (ζ : RealTest Set.univ) (A : Fin 3 → Fin 3 → Test)
    (v : L2Scalar) (G F : L2Vector) (d : ℝ) (hd : 0 ≤ d) (j : Fin 3) :
    flux A (localizedGradient ζ v G) d hd j - localizedForcing ζ A v F d hd j =
      cutScalar ζ (flux A G d hd j - F j) := by
  unfold localizedGradient localizedForcing
  rw [flux_add, cutScalar_sub, cutoff_flux_commute]
  abel

theorem localize_regional_scalar_equation (V S : Set Space) (A : Fin 3 → Fin 3 → Test)
    (v : L2Scalar) (G F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hgrad : ∀ j, HasPartialOn V v (G j) j)
    (hdiv : HasDivergenceOn V (fun j => flux A G d hd j - F j) 0)
    (ζ : RealTest Set.univ) (hζV : tsupport ζ.function ⊆ V)
    (hζS : ∀ x ∈ S, ζ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) :
    (∀ j, HasWeakPartial (cutScalar ζ v) (localizedGradient ζ v G j) j) ∧
    HasWeakDivergence (fun j => flux A (localizedGradient ζ v G) d hd j - localizedForcing ζ A v F d hd j)
      (cutFluxSource ζ.complexTest.toTest (fun j => flux A G d hd j - F j)) ∧
    (∀ᵐ x ∂volume, x ∈ S → cutFluxSource ζ.complexTest.toTest (fun j => flux A G d hd j - F j) x = 0) ∧
    CompactRepresentative (cutScalar ζ v) ∧
    ∀ j, CompactRepresentative (localizedForcing ζ A v F d hd j) := by
  have hζV' : tsupport ζ.complexTest.function ⊆ V := by
    simpa only [RealTest.complexTest, tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero] using hζV
  have hζS' : ∀ x ∈ S, ζ.complexTest.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    intro x hx
    filter_upwards [hζS x hx] with y hy
    simp [RealTest.complexTest,hy]
  refine ⟨?_,?_,cutoff_source_vanishes_on ζ.complexTest.toTest _ S hζS',cutoff_compact ζ.complexTest.toTest v,?_⟩
  · intro j
    exact local_cutoff_weak_partial V ζ.complexTest.toTest hζV' v (G j) j (hgrad j)
  · have hh := regional_flux_cutoff_divergence V (fun j => flux A G d hd j-F j) hdiv ζ.complexTest.toTest hζV'
    have he : (fun j => flux A (localizedGradient ζ v G) d hd j - localizedForcing ζ A v F d hd j) =
        cutFlux ζ.complexTest.toTest (fun j => flux A G d hd j-F j) := by
      funext j
      exact localized_scalar_flux_identity ζ A v G F d hd j
    rw [he]
    exact hh
  · intro j
    apply compact_add
    · exact cutoff_compact ζ.complexTest.toTest (F j)
    · exact weight_compact d hd _ (matrixField_compact A (cutoffCorrection ζ v) j)

end OQ14.Packet05RegionalScalarLocalization
#print axioms OQ14.Packet05RegionalScalarLocalization.localized_scalar_flux_identity
#print axioms OQ14.Packet05RegionalScalarLocalization.localize_regional_scalar_equation
