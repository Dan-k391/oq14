import HarmonicMomentCoupling

noncomputable section
set_option autoImplicit false
namespace OQ14.HarmonicMomentIntegrability
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.HarmonicMomentCoupling MvPolynomial
open scoped Topology

theorem radial_weight_continuous (p : HarmonicPolynomial.Poly) (j : Fin 3) :
    Continuous (radialWeight p j) := by
  exact (Complex.continuous_ofReal.comp ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp continuous_subtype_val)).mul
    (angularPolynomial_continuous p)

theorem radial_integrable (f : ScalarL2) (σ : Sphere → ℂ) (hσ : Continuous σ)
    (hσlp : MemLp σ 2 angularMeasure) (η : ℝ → ℂ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (m : ℕ) :
    IntegrableOn (fun r : ℝ => (r : ℂ)^(m+1) * η r * moment f σ r) (Ioi 0) := by
  have hw := radial_moment_memLp f σ hσ.measurable hσlp
  have hfactor : MemLp (fun r : ℝ => (r : ℂ)^m * η r) 2 (volume.restrict (Ioi 0)) := by
    exact (((Complex.continuous_ofReal.pow m).mul hη.continuous).memLp_of_hasCompactSupport hc.mul_left).restrict _
  have hi := hfactor.integrable_mul hw
  change Integrable (fun r : ℝ => (r : ℂ)^(m+1) * η r * moment f σ r) (volume.restrict (Ioi 0))
  convert hi using 1
  funext r
  simp only [Pi.mul_apply, pow_succ]
  ring

#print axioms OQ14.HarmonicMomentIntegrability.radial_weight_continuous
#print axioms OQ14.HarmonicMomentIntegrability.radial_integrable
end OQ14.HarmonicMomentIntegrability

namespace OQ14.HarmonicMomentIntegrability
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.HarmonicMomentCoupling OQ14.ComplexKernelResponse MvPolynomial
open scoped Topology

def radialMoment (E : Fin 3 → ScalarL2) (p : HarmonicPolynomial.Poly) (r : ℝ) : ℂ :=
  ∑ j : Fin 3, moment (E j) (radialWeight p j) r

def gradientMoment (E : Fin 3 → ScalarL2) (p : HarmonicPolynomial.Poly) (r : ℝ) : ℂ :=
  ∑ j : Fin 3, moment (E j) (gradientWeight p j) r

theorem actual_weak_relation (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) 1)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) :
    let E := fun j => NewtonL2.physicalCoordinate (response (ModalWeightedMode.coefficient n hn) z 1 u) j
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3) * deriv η r * radialMoment E p r) +
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * gradientMoment E p r) = 0 := by
  dsimp only
  let E := fun j => NewtonL2.physicalCoordinate (response (ModalWeightedMode.coefficient n hn) z 1 u) j
  have hη' : ContDiff ℝ (⊤ : ℕ∞) (deriv η) := (contDiff_infty_iff_deriv.mp hη).2
  have hA (j : Fin 3) : IntegrableOn (fun r : ℝ => (r : ℂ)^(l+3) * deriv η r * moment (E j) (radialWeight p j) r) (Ioi 0) := by
    simpa only [show l+3 = (l+2)+1 by omega] using radial_integrable (E j) (radialWeight p j)
      (radial_weight_continuous p j) (weight_memLp p j).1 (deriv η) hη' hc.deriv (l+2)
  have hB (j : Fin 3) : IntegrableOn (fun r : ℝ => (r : ℂ)^(l+2) * η r * moment (E j) (gradientWeight p j) r) (Ioi 0) := by
    simpa only [show l+2 = (l+1)+1 by omega] using radial_integrable (E j) (gradientWeight p j)
      (angularPolynomial_continuous _) (weight_memLp p j).2 η hη hc (l+1)
  have h := actual_moment_divergence n hn z hz u hker η hη hc hs p l hp
  have hrewrite (j : Fin 3) :
      (∫ r in Ioi (0 : ℝ), (r^2 : ℂ) *
        ((deriv η r * (r : ℂ)^(l+1)) * moment (E j) (radialWeight p j) r +
         (η r * (r : ℂ)^l) * moment (E j) (gradientWeight p j) r)) =
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3) * deriv η r * moment (E j) (radialWeight p j) r) +
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * moment (E j) (gradientWeight p j) r) := by
    rw [← integral_add (hA j) (hB j)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [pow_add, pow_succ]
    ring
  change (∑ j : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ) *
        ((deriv η r * (r : ℂ)^(l+1)) * moment (E j) (radialWeight p j) r +
         (η r * (r : ℂ)^l) * moment (E j) (gradientWeight p j) r)) = 0 at h
  simp_rw [hrewrite] at h
  rw [Finset.sum_add_distrib] at h
  have hleft : (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3) * deriv η r * radialMoment E p r) =
      ∑ j : Fin 3, ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3) * deriv η r * moment (E j) (radialWeight p j) r := by
    rw [← integral_finset_sum _ (fun j _ => hA j)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp [radialMoment, Finset.mul_sum]
  have hright : (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * gradientMoment E p r) =
      ∑ j : Fin 3, ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * moment (E j) (gradientWeight p j) r := by
    rw [← integral_finset_sum _ (fun j _ => hB j)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp [gradientMoment, Finset.mul_sum]
  rw [hleft, hright]
  exact h

#print axioms OQ14.HarmonicMomentIntegrability.actual_weak_relation
end OQ14.HarmonicMomentIntegrability

namespace OQ14.HarmonicMomentIntegrability
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.PolarMomentEnergy OQ14.ComplexKernelResponse MvPolynomial

def tangentialMoment (E : Fin 3 → ScalarL2) (p : HarmonicPolynomial.Poly) (l : ℕ) (r : ℝ) : ℂ :=
  gradientMoment E p r - (l+1 : ℂ) * radialMoment E p r

theorem actual_radial_tangential_relation (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) 1)
    (p : HarmonicPolynomial.Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) :
    let E := fun j => NewtonL2.physicalCoordinate (response (ModalWeightedMode.coefficient n hn) z 1 u) j
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3) * deriv η r * radialMoment E p r) +
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r *
        (tangentialMoment E p l r + (l+1 : ℂ) * radialMoment E p r)) = 0 := by
  simpa only [tangentialMoment, sub_add_cancel] using
    actual_weak_relation n hn z hz u hker η hη hc hs p l hp

#print axioms OQ14.HarmonicMomentIntegrability.actual_radial_tangential_relation
end OQ14.HarmonicMomentIntegrability
