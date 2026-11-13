import KernelRadialMomentBridge
import Packet01WeakDerivative
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.Packet04TMWeakReduction
open Complex MeasureTheory Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability
open scoped Topology

theorem div_radial_pow_test (T : ℝ)
    (L : ℕ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => ψ r / (r : ℂ)^L) ∧
    HasCompactSupport (fun r : ℝ => ψ r / (r : ℂ)^L) ∧
    tsupport (fun r : ℝ => ψ r / (r : ℂ)^L) ⊆ Ioo (0 : ℝ) T ∧
    ∀ r ∈ Ioi (0 : ℝ),
      HasDerivAt (fun t : ℝ => ψ t / (t : ℂ)^L)
        (deriv ψ r / (r : ℂ)^L - (L : ℂ) * ψ r / (r : ℂ)^(L+1)) r := by
  have hsub : tsupport (fun r : ℝ => ψ r / (r : ℂ)^L) ⊆ tsupport ψ := by
    simpa only [div_eq_mul_inv] using (tsupport_mul_subset_left (f := ψ) (g := fun r : ℝ => ((r : ℂ)^L)⁻¹))
  have h0 : (0 : ℝ) ∉ tsupport ψ := fun h => (hs h).1.false
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => ψ r / (r : ℂ)^L) := by
    apply contDiff_iff_contDiffAt.mpr
    intro r
    by_cases hr : r = 0
    · subst r
      have hz : ψ =ᶠ[𝓝 (0 : ℝ)] 0 := by
        filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds h0] with s h
        exact image_eq_zero_of_nmem_tsupport h
      have he : (fun r : ℝ => ψ r / (r : ℂ)^L) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
        filter_upwards [hz] with s h
        simp only [h, Pi.zero_apply, zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq he
    · have hi : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => ((t : ℂ)^L)⁻¹) r := ((Complex.ofRealCLM.contDiff.contDiffAt.pow L).inv (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hr)))
      simpa only [div_eq_mul_inv] using hψ.contDiffAt.mul hi
  refine ⟨hsm, hc.of_isClosed_subset (isClosed_tsupport _) hsub, hsub.trans hs, ?_⟩
  intro r hr
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hd := hψ.differentiable (by simp) r |>.hasDerivAt
  have hx : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
  have hi0 : HasDerivAt (fun z : ℂ => z⁻¹) (-((r : ℂ)^2)⁻¹) (r : ℂ) := hasDerivAt_inv hr0
  have hi := (hi0.pow L).comp r hx
  have hh := hd.mul hi
  convert hh using 1 <;> simp only [div_eq_mul_inv, inv_pow, one_mul]
  simp only [Function.comp_def]
  cases L with | zero => simp | succ L => simp only [Nat.succ_sub_one, pow_succ, Nat.cast_succ, Function.comp_def]; ring

private theorem test_integral_eq (η : ℝ → ℂ) (hs : tsupport η ⊆ Ioi (0 : ℝ)) (f : ℝ → ℂ) :
    (∫ r in Ioi (0 : ℝ), η r * f r) = ∫ r, η r * f r := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  have hn : r ∉ tsupport η := fun h => hr (hs h)
  simp only [image_eq_zero_of_nmem_tsupport hn, zero_mul]

private theorem test_deriv_support (η : ℝ → ℂ) : tsupport (deriv η) ⊆ tsupport η :=
  (closure_mono support_deriv_subset).trans (by simp only [tsupport, isClosed_closure.closure_eq, subset_refl])

private theorem radial_test_integrable (E : Fin 3 → ScalarL2) (p : Poly)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (m : ℕ) :
    IntegrableOn (fun r : ℝ => (r : ℂ)^(m+1) * η r * radialMoment E p r) (Ioi 0) := by
  have hi (j : Fin 3) := radial_integrable (E j) (radialWeight p j)
    (radial_weight_continuous p j) (weight_memLp p j).1 η hη hc m
  have hsum := integrable_finset_sum Finset.univ (fun j _ => hi j)
  change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
  convert hsum using 1
  funext r
  simp [radialMoment, Finset.mul_sum]

private theorem gradient_test_integrable (E : Fin 3 → ScalarL2) (p : Poly)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (m : ℕ) :
    IntegrableOn (fun r : ℝ => (r : ℂ)^(m+1) * η r * gradientMoment E p r) (Ioi 0) := by
  have hi (j : Fin 3) := radial_integrable (E j) (gradientWeight p j)
    (angularPolynomial_continuous _) (weight_memLp p j).2 η hη hc m
  have hsum := integrable_finset_sum Finset.univ (fun j _ => hi j)
  change Integrable _ (volume.restrict (Ioi (0 : ℝ)))
  convert hsum using 1
  funext r
  simp [gradientMoment, Finset.mul_sum]

theorem radial_tangential_weak (T : ℝ) (E : Fin 3 → ScalarL2) (p : Poly) (l : ℕ)
    (hrelation : ∀ η : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo (0 : ℝ) T →
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3)*deriv η r*radialMoment E p r) +
        (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2)*η r*gradientMoment E p r) = 0)
    (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Ioo (0 : ℝ) T) :
    (∫ r : ℝ, deriv ψ r * ((r : ℂ)^2 * radialMoment E p r)) +
      (∫ r : ℝ, ψ r * ((r : ℂ) * tangentialMoment E p l r)) = 0 := by
  let η : ℝ → ℂ := fun r => ψ r / (r : ℂ)^(l+1)
  obtain ⟨hη, hηc, hηs, hηd⟩ := div_radial_pow_test T (l+1) ψ hψ hc hs
  have hψd : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hx := radial_test_integrable E p (deriv ψ) hψd hc.deriv 1
  have hy := (radial_test_integrable E p ψ hψ hc 0).const_mul (l+1 : ℂ)
  have hz' := gradient_test_integrable E p ψ hψ hc 0
  have hw := hrelation η hη hηc hηs
  change (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3) * deriv η r * radialMoment E p r) +
    (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * gradientMoment E p r) = 0 at hw
  have he1 : (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3) * deriv η r * radialMoment E p r) =
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^2 * deriv ψ r * radialMoment E p r) -
      (∫ r in Ioi (0 : ℝ), (l+1 : ℂ) * ((r : ℂ)^1 * ψ r * radialMoment E p r)) := by
    rw [← integral_sub hx hy]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hd := (hηd r hr).deriv
    dsimp only [η]
    rw [hd]
    push_cast
    field_simp
    ring
  have he2 : (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2) * η r * gradientMoment E p r) =
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^1 * ψ r * gradientMoment E p r) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    dsimp [η]
    field_simp
    ring
  rw [he1, he2] at hw
  have ht : (∫ r in Ioi (0 : ℝ), ψ r * ((r : ℂ) * tangentialMoment E p l r)) =
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^1 * ψ r * gradientMoment E p r) -
      (∫ r in Ioi (0 : ℝ), (l+1 : ℂ) * ((r : ℂ)^1 * ψ r * radialMoment E p r)) := by
    rw [← integral_sub hz' hy]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    simp only [tangentialMoment, pow_one, Nat.cast_add, Nat.cast_one]
    ring
  have hs' : tsupport ψ ⊆ Ioi (0 : ℝ) := hs.trans (fun _ h => h.1)
  have hs'' : tsupport (deriv ψ) ⊆ Ioi (0 : ℝ) := (test_deriv_support ψ).trans hs'
  rw [test_integral_eq ψ hs'] at ht
  have hleft : (∫ r in Ioi (0 : ℝ), (r : ℂ)^2 * deriv ψ r * radialMoment E p r) =
      ∫ r : ℝ, deriv ψ r * ((r : ℂ)^2 * radialMoment E p r) := by
    rw [← test_integral_eq (deriv ψ) hs'']
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    ring
  rw [hleft] at hw
  change (∫ r : ℝ, deriv ψ r * ((r : ℂ)^2 * radialMoment E p r)) +
    (∫ r : ℝ, ψ r * ((r : ℂ) * tangentialMoment E p l r)) = 0
  rw [ht]
  linear_combination hw

theorem weak_derivative (T : ℝ) (E : Fin 3 → ScalarL2) (p : Poly) (l : ℕ)
    (hrelation : ∀ η : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo (0 : ℝ) T →
      (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+3)*deriv η r*radialMoment E p r) +
        (∫ r in Ioi (0 : ℝ), (r : ℂ)^(l+2)*η r*gradientMoment E p r) = 0) :
    SmoothWeakDerivative.WeakDerivative (Ioo (0 : ℝ) T)
      (fun r => (r : ℂ)^2 * radialMoment E p r)
      (fun r => (r : ℂ) * tangentialMoment E p l r) :=
  Packet01WeakDerivative.of_complex_tests _ _ _ (radial_tangential_weak T E p l hrelation)

end OQ14.Packet04TMWeakReduction
#print axioms OQ14.Packet04TMWeakReduction.div_radial_pow_test
#print axioms OQ14.Packet04TMWeakReduction.radial_tangential_weak
#print axioms OQ14.Packet04TMWeakReduction.weak_derivative
