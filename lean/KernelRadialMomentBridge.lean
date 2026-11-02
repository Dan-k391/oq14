import HarmonicMomentIntegrability
import ComplexKernelDebye

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.KernelRadialMomentBridge
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.PolarMomentTesting OQ14.PolarMomentEnergy
  OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability
  OQ14.ComplexKernelResponse MvPolynomial
open scoped Topology

theorem radial_moment_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2)
    (p : HarmonicPolynomial.Poly) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      radialMoment (ComplexKernelDebye.coordinates n hn z u) p r =
        ComplexKernelDebye.radialCoefficient n hn z u p r := by
  let E := response (ModalWeightedMode.coefficient n hn) z 1 u
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun r hr => hr.1
  have hi : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ j : Fin 3,
      Integrable (fun ω : Sphere => NewtonL2.physicalCoordinate E j (r • (ω : Space)) * radialWeight p j ω) angularMeasure := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [slice_memLp_ae (NewtonL2.physicalCoordinate E j)] with r hr
    exact hr.integrable_mul (weight_memLp p j).1
  have hj (j : Fin 3) : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ᵐ ω : Sphere ∂angularMeasure,
      NewtonL2.physicalCoordinate E j (r • (ω : Space)) =
        E (VectorFourier.coordinateMap (r • (ω : Space))) j := by
    have hcoord : ∀ᵐ x : Space ∂volume, NewtonL2.physicalCoordinate E j x = E (VectorFourier.coordinateMap x) j := NewtonL2.physicalCoordinate_ae E j
    exact OQ14.PolarMomentAE.polar_ae (P := fun x : Space => NewtonL2.physicalCoordinate E j x = E (VectorFourier.coordinateMap x) j) hcoord
  have he : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ᵐ ω : Sphere ∂angularMeasure,
      ∀ j : Fin 3, NewtonL2.physicalCoordinate E j (r • (ω : Space)) =
        E (VectorFourier.coordinateMap (r • (ω : Space))) j := by
    filter_upwards [ae_all_iff.mpr hj] with r hr
    exact ae_all_iff.mpr hr
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hi,
    ae_restrict_of_ae_restrict_of_subset hsub he] with r hr he
  have hs : (∑ j : Fin 3, ∫ ω : Sphere, NewtonL2.physicalCoordinate E j (r • (ω : Space)) * radialWeight p j ω ∂angularMeasure) =
      ComplexKernelDebye.radialCoefficient n hn z u p r := by
    rw [← integral_finset_sum _ (fun j _ => hr j)]
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    change (∑ j : Fin 3, NewtonL2.physicalCoordinate E j (r • (ω : Space)) * radialWeight p j ω) =
      (∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) * E (VectorFourier.coordinateMap (r • (ω : Space))) j) *
        SphericalMomentEquation.angularPolynomial p ω
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [hω j]
    dsimp [radialWeight]
    ring
  exact hs

#print axioms OQ14.KernelRadialMomentBridge.radial_moment_actual
end OQ14.KernelRadialMomentBridge

namespace OQ14.KernelRadialMomentBridge
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.PolarMomentTesting OQ14.PolarMomentEnergy
  OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability OQ14.ComplexKernelResponse MvPolynomial
open scoped Topology

theorem tangential_moment_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2)
    (p : HarmonicPolynomial.Poly) (l : ℕ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      tangentialMoment (ComplexKernelDebye.coordinates n hn z u) p l r =
        ∫ ω : Sphere, ∑ j : Fin 3,
          response (ModalWeightedMode.coefficient n hn) z 1 u
            (VectorFourier.coordinateMap (r • (ω : Space))) j *
          (gradientWeight p j ω - (l+1 : ℂ) * radialWeight p j ω) ∂angularMeasure := by
  let E := response (ModalWeightedMode.coefficient n hn) z 1 u
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun r hr => hr.1
  have hs : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ j : Fin 3,
      MemLp (fun ω : Sphere => NewtonL2.physicalCoordinate E j (r • (ω : Space))) 2 angularMeasure :=
    ae_all_iff.mpr (fun j => slice_memLp_ae _)
  have he : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ᵐ ω : Sphere ∂angularMeasure,
      ∀ j : Fin 3, NewtonL2.physicalCoordinate E j (r • (ω : Space)) =
        E (VectorFourier.coordinateMap (r • (ω : Space))) j := by
    filter_upwards [ae_all_iff.mpr (fun j => OQ14.PolarMomentAE.polar_ae (NewtonL2.physicalCoordinate_ae E j))] with r hr
    exact ae_all_iff.mpr hr
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hs,
    ae_restrict_of_ae_restrict_of_subset hsub he] with r hr he
  have hi (j : Fin 3) : Integrable (fun ω : Sphere => NewtonL2.physicalCoordinate E j (r • (ω : Space)) *
      (gradientWeight p j ω - (l+1 : ℂ) * radialWeight p j ω)) angularMeasure := by
    exact (hr j).integrable_mul ((weight_memLp p j).2.sub ((weight_memLp p j).1.const_mul _))

  have ha (j : Fin 3) : (∫ ω : Sphere, NewtonL2.physicalCoordinate E j (r • (ω : Space)) *
      (gradientWeight p j ω - (l+1 : ℂ) * radialWeight p j ω) ∂angularMeasure) =
      moment (NewtonL2.physicalCoordinate E j) (gradientWeight p j) r -
        (l+1 : ℂ) * moment (NewtonL2.physicalCoordinate E j) (radialWeight p j) r := by
    have h1 := (hr j).integrable_mul (weight_memLp p j).2
    have h2 := ((hr j).integrable_mul (weight_memLp p j).1).const_mul (l+1 : ℂ)
    have heq : (fun ω : Sphere => NewtonL2.physicalCoordinate E j (r • (ω : Space)) *
      (gradientWeight p j ω - (l+1 : ℂ) * radialWeight p j ω)) =
      (fun ω : Sphere => NewtonL2.physicalCoordinate E j (r • (ω : Space)) * gradientWeight p j ω -
        (l+1 : ℂ) * (NewtonL2.physicalCoordinate E j (r • (ω : Space)) * radialWeight p j ω)) := by
      funext ω
      ring
    change Integrable (fun ω : Sphere => NewtonL2.physicalCoordinate E j (r • (ω : Space)) * gradientWeight p j ω) angularMeasure at h1
    change Integrable (fun ω : Sphere => (l+1 : ℂ) * (NewtonL2.physicalCoordinate E j (r • (ω : Space)) * radialWeight p j ω)) angularMeasure at h2
    rw [heq, integral_sub h1 h2, integral_const_mul]
    rfl
  calc
    _ = ∑ j : Fin 3, ∫ ω : Sphere, NewtonL2.physicalCoordinate E j (r • (ω : Space)) *
        (gradientWeight p j ω - (l+1 : ℂ) * radialWeight p j ω) ∂angularMeasure := by
          simp only [tangentialMoment, gradientMoment, radialMoment, Finset.mul_sum, ← Finset.sum_sub_distrib, ha, ComplexKernelDebye.coordinates, E]
    _ = _ := by
      rw [← integral_finset_sum _ (fun j _ => hi j)]
      apply integral_congr_ae
      filter_upwards [he] with ω hω
      apply Finset.sum_congr rfl
      intro j _
      rw [hω j]

#print axioms OQ14.KernelRadialMomentBridge.tangential_moment_actual
end OQ14.KernelRadialMomentBridge
