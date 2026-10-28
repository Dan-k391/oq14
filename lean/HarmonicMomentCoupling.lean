import ComplexSphereMomentDivergence
import PolarMomentEnergy
import PolarMomentAE

noncomputable section
set_option autoImplicit false
namespace OQ14.HarmonicMomentCoupling
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy MvPolynomial
open scoped Topology

def radialWeight (p : HarmonicPolynomial.Poly) (j : Fin 3) (ω : Sphere) : ℂ :=
  (((ω : Space) j : ℝ) : ℂ) * angularPolynomial p ω

def gradientWeight (p : HarmonicPolynomial.Poly) (j : Fin 3) (ω : Sphere) : ℂ :=
  angularPolynomial (pderiv j p) ω

theorem weight_memLp (p : HarmonicPolynomial.Poly) (j : Fin 3) :
    MemLp (radialWeight p j) 2 angularMeasure ∧ MemLp (gradientWeight p j) 2 angularMeasure := by
  have hc : Continuous (fun ω : Sphere => (((ω : Space) j : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp continuous_subtype_val)
  constructor
  · exact (hc.mul (angularPolynomial_continuous p)).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (angularPolynomial_continuous _).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem angular_split (f : ScalarL2) (p : HarmonicPolynomial.Poly) (j : Fin 3) (r : ℝ)
    (A B : ℂ) (hf : MemLp (fun ω : Sphere => f (r • (ω : Space))) 2 angularMeasure) :
    (∫ ω : Sphere, f (r • (ω : Space)) *
      (A * (((ω : Space) j : ℝ) : ℂ) * angularPolynomial p ω +
       B * angularPolynomial (pderiv j p) ω) ∂angularMeasure) =
      A * moment f (radialWeight p j) r + B * moment f (gradientWeight p j) r := by
  have h := weight_memLp p j
  have h1 := (hf.integrable_mul h.1).const_mul A
  have h2 := (hf.integrable_mul h.2).const_mul B
  change Integrable (fun ω : Sphere => A * (f (r • (ω : Space)) * radialWeight p j ω)) angularMeasure at h1
  change Integrable (fun ω : Sphere => B * (f (r • (ω : Space)) * gradientWeight p j ω)) angularMeasure at h2
  have he : (fun ω : Sphere => f (r • (ω : Space)) *
      (A * (((ω : Space) j : ℝ) : ℂ) * angularPolynomial p ω +
       B * angularPolynomial (pderiv j p) ω)) =
      fun ω : Sphere => A * (f (r • (ω : Space)) * radialWeight p j ω) +
        B * (f (r • (ω : Space)) * gradientWeight p j ω) := by
    funext ω
    dsimp [radialWeight, gradientWeight]
    ring
  rw [he, integral_add h1 h2, integral_const_mul, integral_const_mul]
  rfl

#print axioms OQ14.HarmonicMomentCoupling.weight_memLp
#print axioms OQ14.HarmonicMomentCoupling.angular_split
end OQ14.HarmonicMomentCoupling

namespace OQ14.HarmonicMomentCoupling
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.ComplexKernelResponse MvPolynomial
open scoped Topology

theorem actual_moment_divergence (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) 1)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) :
    (∑ j : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ) *
      ((deriv η r * (r : ℂ)^(l+1)) * moment
        (NewtonL2.physicalCoordinate (response (ModalWeightedMode.coefficient n hn) z 1 u) j) (radialWeight p j) r +
       (η r * (r : ℂ)^l) * moment
        (NewtonL2.physicalCoordinate (response (ModalWeightedMode.coefficient n hn) z 1 u) j) (gradientWeight p j) r)) = 0 := by
  let E := response (ModalWeightedMode.coefficient n hn) z 1 u
  have h := ComplexSphereMomentDivergence.harmonic_radial_coupling n hn z hz u hker η hη hc hs p l hp
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [slice_memLp_ae (NewtonL2.physicalCoordinate E j),
    OQ14.PolarMomentAE.polar_ae (NewtonL2.physicalCoordinate_ae E j)] with r hr he
  apply congrArg (fun t : ℂ => (r^2 : ℂ) * t)
  rw [← angular_split (NewtonL2.physicalCoordinate E j) p j r
    (deriv η r * (r : ℂ)^(l+1)) (η r * (r : ℂ)^l) hr]
  apply integral_congr_ae
  filter_upwards [he] with ω hω
  rw [hω]
  congr 1
  ring

#print axioms OQ14.HarmonicMomentCoupling.actual_moment_divergence
end OQ14.HarmonicMomentCoupling
