import Packet04TMFirstDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet04TMSecondDerivative
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.HarmonicMomentIntegrability OQ14.Packet04TMMoments
open scoped Topology

private theorem test_integrable (T : ℝ) (f : ℝ → ℂ)
    (hf : LocallyIntegrableOn f (Ioo (0 : ℝ) T)) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioo (0 : ℝ) T) :
    Integrable (fun r => ψ r * f r) := by
  have hi := (hf.integrableOn_compact_subset hs hc).continuousOn_mul hψ.continuousOn hc
  rw [← integrableOn_iff_integrable_of_support_subset (s := tsupport ψ)]
  · exact hi
  · intro r hr
    by_contra hn
    apply hr
    simp [image_eq_zero_of_nmem_tsupport hn]

/-- The second actual TM weak derivative, across the dielectric interface. -/
theorem actual_second_weak_derivative (n : ℝ) (hn : 1 < n) (z : ℂ)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorFourier.VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock
      (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0) :
    SmoothWeakDerivative.WeakDerivative (Ioo (0 : ℝ) T)
      (fun r => (r : ℂ) * tangentialMoment (electricCoordinates n hn z T u) p l r)
      (fun r => (l+1 : ℂ)*(l+2 : ℂ)*electricRadial n hn z T u p r -
        z^2*(r : ℂ)^2*displacementRadial n hn z T u p r) := by
  apply Packet01WeakDerivative.of_complex_tests
  intro ψ hψ hc hs
  let E := electricCoordinates n hn z T u
  let A := electricRadial n hn z T u p
  let B := tangentialMoment E p l
  let D := displacementRadial n hn z T u p
  let η : ℝ → ℂ := fun r => ψ r / (r : ℂ)^(l+2)
  obtain ⟨hη,hηc,hηs,hηd⟩ := Packet04TMWeakReduction.div_radial_pow_test T (l+2) ψ hψ hc hs
  have h := electric_toroidal_weak n hn z T hT u hker p l hp hh η hη hηc hηs
  have hm : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), r ∈ Ioo (0 : ℝ) T →
      magneticCoefficient n hn z T u p r = -(I*z)*(r : ℂ)*D r :=
    ae_restrict_of_ae ((ae_restrict_iff' measurableSet_Ioo).mp
      (magnetic_displacement_coefficient n hn z T hT u hker p (l+1) hp))
  have hright : (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3)*η r *
      magneticCoefficient n hn z T u p r) =
      -(I*z) * ∫ r in Ioi (0 : ℝ), ψ r * ((r : ℂ)^2*D r) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hm, ae_restrict_mem measurableSet_Ioi] with r hr hr0
    change 0 < r at hr0
    by_cases hrt : r < T
    · rw [hr ⟨hr0,hrt⟩]
      have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr0.ne'
      dsimp [η]
      field_simp [hrne]
      ring
    · have hn0 : r ∉ tsupport ψ := fun ht => hrt (hs ht).2
      have hz : ψ r = 0 := image_eq_zero_of_nmem_tsupport hn0
      simp [η, hz]
  have hleft : (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) *
      (((r : ℂ)*deriv η r+(l+2 : ℂ)*η r) *
        (electricGradient n hn z T u p r - (l+1 : ℂ)*A r) +
       (l+1 : ℂ)*(l+2 : ℂ)*η r*A r)) =
      ∫ r in Ioi (0 : ℝ), deriv ψ r * ((r : ℂ)*B r) +
        ψ r * ((l+1 : ℂ)*(l+2 : ℂ)*A r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hd := (hηd r hr).deriv
    dsimp only [η]
    rw [hd]
    dsimp [A, B, E, electricGradient, electricRadial, tangentialMoment]
    field_simp [hrne]
    ring
  rw [hleft, hright] at h
  have hBl := (Packet01MomentIntegrability.tangentialMoment_locallyIntegrableOn E p l).mono_set
    (show Ioo (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  have hAl := (Packet01MomentIntegrability.radialMoment_locallyIntegrableOn E p).mono_set
    (show Ioo (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  have hDl := (displacementRadial_local n hn z T u p).mono_set
    (show Ioo (0 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => hr.1)
  have hFl : LocallyIntegrableOn (fun r : ℝ => (r : ℂ)*B r) (Ioo (0 : ℝ) T) :=
    hBl.continuousOn_mul Complex.continuous_ofReal.continuousOn isOpen_Ioo.isLocallyClosed
  have hGl : LocallyIntegrableOn (fun r : ℝ => (l+1 : ℂ)*(l+2 : ℂ)*A r) (Ioo (0 : ℝ) T) :=
    hAl.continuousOn_mul continuousOn_const isOpen_Ioo.isLocallyClosed
  have hUl : LocallyIntegrableOn (fun r : ℝ => (r : ℂ)^2*D r) (Ioo (0 : ℝ) T) :=
    hDl.continuousOn_mul (Complex.continuous_ofReal.pow 2).continuousOn isOpen_Ioo.isLocallyClosed
  have hψd : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hsd : tsupport (deriv ψ) ⊆ Ioo (0 : ℝ) T :=
    ((closure_mono support_deriv_subset).trans (by simp only [tsupport, isClosed_closure.closure_eq, subset_refl])).trans hs
  have hi1 := test_integrable T _ hFl (deriv ψ) hψd.continuous hc.deriv hsd
  have hi2 := test_integrable T _ hGl ψ hψ.continuous hc hs
  have hi3 := test_integrable T _ hUl ψ hψ.continuous hc hs
  rw [integral_add hi1.integrableOn hi2.integrableOn] at h
  have hcplx : I*z * (-(I*z)) = z^2 := by ring_nf; simp [Complex.I_sq]
  rw [← mul_assoc, hcplx] at h
  have hsub : (∫ r : ℝ, ψ r * ((l+1 : ℂ)*(l+2 : ℂ)*A r-z^2*(r : ℂ)^2*D r)) =
      (∫ r : ℝ, ψ r * ((l+1 : ℂ)*(l+2 : ℂ)*A r)) - z^2 *
        (∫ r : ℝ, ψ r * ((r : ℂ)^2*D r)) := by
    rw [← integral_const_mul, ← integral_sub hi2 (hi3.const_mul _)]
    apply integral_congr_ae
    filter_upwards with r
    ring
  have hpos1 : (∫ r in Ioi (0 : ℝ), deriv ψ r * ((r : ℂ)*B r)) = ∫ r : ℝ, deriv ψ r * ((r : ℂ)*B r) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hn0 : r ∉ tsupport (deriv ψ) := fun ht => hr (hsd ht).1
    simp [image_eq_zero_of_nmem_tsupport hn0]
  have hpos2 (f : ℝ → ℂ) : (∫ r in Ioi (0 : ℝ), ψ r * f r) = ∫ r : ℝ, ψ r * f r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    have hn0 : r ∉ tsupport ψ := fun ht => hr (hs ht).1
    simp [image_eq_zero_of_nmem_tsupport hn0]
  rw [hpos1, hpos2, hpos2] at h
  change (∫ r : ℝ, deriv ψ r * ((r : ℂ)*B r)) +
    (∫ r : ℝ, ψ r * ((l+1 : ℂ)*(l+2 : ℂ)*A r-z^2*(r : ℂ)^2*D r)) = 0
  rw [hsub]
  linear_combination h

#print axioms OQ14.Packet04TMSecondDerivative.actual_second_weak_derivative

#print axioms OQ14.Packet04TMSecondDerivative.test_integrable
end OQ14.Packet04TMSecondDerivative
