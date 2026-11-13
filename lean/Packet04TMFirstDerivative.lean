import Packet04TMMoments
import Packet04TMWeakReduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet04TMFirstDerivative
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.HarmonicMomentIntegrability OQ14.Packet04TMMoments
open scoped Topology

/-- First TM weak derivative, obtained from the actual magnetic Maxwell
projection and radial displacement identity. -/
theorem actual_first_weak_derivative (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) :
    SmoothWeakDerivative.WeakDerivative (Ioo (0 : ℝ) T)
      (fun r => (r : ℂ)^2 * displacementRadial n hn z T u p r)
      (fun r => (r : ℂ) * tangentialMoment (displacementCoordinates n hn z T u) p l r) := by
  apply Packet04TMWeakReduction.weak_derivative T (displacementCoordinates n hn z T u) p l
  intro η hη hc hs
  have hm : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Ioo (0 : ℝ) T →
      magneticCoefficient n hn z T u p r = -(I*z)*(r : ℂ)*displacementRadial n hn z T u p r :=
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp
      (magnetic_displacement_coefficient n hn z T hT u hker p (l+1) hp))
  have h := magnetic_gradient_weak n hn z T hT u hker p l hp η hη hc hs
  have he : (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * deriv η r *
      magneticCoefficient n hn z T u p r) = -(I*z) *
      ∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3) * deriv η r * displacementRadial n hn z T u p r := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hm, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    by_cases hrt : r < T
    · rw [hr ⟨hr0,hrt⟩]
      simp only [pow_succ]
      ring
    · have hn0 : r ∉ tsupport η := fun ht => hrt (hs ht).2
      have hd : deriv η r = 0 := by
        simpa only [deriv_zero] using (not_mem_tsupport_iff_eventuallyEq.mp hn0).deriv_eq
      simp [hd]
  rw [he] at h
  change (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3)*deriv η r*
      displacementRadial n hn z T u p r) +
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2)*η r*
      displacementGradient n hn z T u p r) = 0
  have hne : I*z ≠ 0 := mul_ne_zero I_ne_zero hz
  apply (mul_eq_zero.mp ?_).resolve_left hne
  linear_combination -h

#print axioms OQ14.Packet04TMFirstDerivative.actual_first_weak_derivative
end OQ14.Packet04TMFirstDerivative
