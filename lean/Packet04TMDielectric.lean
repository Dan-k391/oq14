import Packet04TMTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04TMDielectric
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.HarmonicMomentIntegrability OQ14.Packet04TMMoments
  OQ14.Packet04WeakSphereMaxwell
open scoped Topology

def radialPermittivity (n : ℝ) (r : ℝ) : ℂ := if r < 1 then (n : ℂ)^2 else 1

theorem displacement_radial_factor (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      displacementRadial n hn z T u p r = radialPermittivity n r * electricRadial n hn z T u p r := by
  filter_upwards [displacementRadial_actual n hn z T hT u hker p,
    electricRadial_actual n hn z T u p, ae_restrict_mem measurableSet_Ioi] with r hd he hr
  change 0 < r at hr
  rw [hd, he, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr]
  simp only [permittivity_value, hnorm, radialPermittivity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem displacement_gradient_factor (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      displacementGradient n hn z T u p r = radialPermittivity n r * electricGradient n hn z T u p r := by
  filter_upwards [displacementGradient_actual n hn z T hT u hker p,
    electricGradient_actual n hn z T u p, ae_restrict_mem measurableSet_Ioi] with r hd he hr
  change 0 < r at hr
  rw [hd, he, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ω
  have hnorm : ‖r • (ω : Space)‖ = r := by simp [norm_smul, sphere_norm, abs_of_pos hr]
  simp only [permittivity_value, hnorm, radialPermittivity, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem displacement_tangential_factor (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      tangentialMoment (displacementCoordinates n hn z T u) p l r =
        radialPermittivity n r * tangentialMoment (electricCoordinates n hn z T u) p l r := by
  filter_upwards [displacement_radial_factor n hn z T hT u hker p,
    displacement_gradient_factor n hn z T hT u hker p] with r hr hg
  change displacementGradient n hn z T u p r - (l+1 : ℂ)*displacementRadial n hn z T u p r =
    radialPermittivity n r * (electricGradient n hn z T u p r - (l+1 : ℂ)*electricRadial n hn z T u p r)
  rw [hg, hr]
  ring

#print axioms OQ14.Packet04TMDielectric.displacement_radial_factor
#print axioms OQ14.Packet04TMDielectric.displacement_gradient_factor
#print axioms OQ14.Packet04TMDielectric.displacement_tangential_factor
end OQ14.Packet04TMDielectric
