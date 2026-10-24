import DyadicKernel
import GreenKernel
import KernelConvolution
import FieldResponse
import MagneticResponse

/-! Dilation identities of the Green kernels and of the kernel responses at frequency `k`.

For `k > 0` and the dilation `x ↦ k • x`:

* the radial profiles `radial`, `radialD`, `radialDD` of frequency `k * κ` at radius `r` are those of frequency `κ` at
  radius `k * r`, times `k`, `k²`, `k³`;
* hence `phi k x = k * phi 1 (k • x)`, `phiGradient k x j = k² * phiGradient 1 (k • x) j`,
  `phiHessian k x i j = k³ * phiHessian 1 (k • x) i j`, `phiHessian 0 x i j = k³ * phiHessian 0 (k • x) i j`,
  `dyadic k x i j = k³ * dyadic 1 (k • x) i j`, `remainder k x i j = k³ * remainder 1 (k • x) i j`
  (all of them for every `x`, the value at the origin being `0` on both sides where it is defined by the division
  convention);
* the change of variables `y' = k • y` in the convolution integral (`Measure.integral_comp_smul`, no hypothesis on the
  source is needed: the identity holds for the integral as a Bochner integral) gives, for the dilated source
  `ρk y = k * ρ (k • y)`, the identities
  `response (remainder k · i j) ρk x = k * response (remainder 1 · i j) ρ (k • x)` and
  `magnetic k (k * ρ (k • ·)) x i = k * magnetic 1 ρ (k • x) i`
  (the kernel `phiGradient` carries `k²`, the Jacobian `k⁻³`, the dilated source `k`, and the magnetic prefactor `-I k`
  gives the last `k`);
* `electric_remainder_scale` packages the sum over the source components, the remainder part of
  `FieldResponse.electric`; `dilated_integrable`, `dilated_hasCompactSupport` give the integrability and compact
  support of the dilated source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.DilationKernels
open MeasureTheory OQ14.Maxwell

/-! ### The radial profiles -/

theorem radial_scale (κ k r : ℝ) (hk : 0 < k) :
    GreenKernel.radial (k * κ) r = (k : ℂ) * GreenKernel.radial κ (k * r) := by
  unfold GreenKernel.radial
  by_cases hr : r = 0
  · simp [hr]
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have e : Complex.I * ((k * κ : ℝ) : ℂ) * (r : ℂ) = Complex.I * (κ : ℂ) * ((k * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e]
  push_cast
  field_simp
  ring

theorem radialD_scale (κ k r : ℝ) (hk : 0 < k) (hr : r ≠ 0) :
    GreenKernel.radialD (k * κ) r = (k : ℂ) ^ 2 * GreenKernel.radialD κ (k * r) := by
  unfold GreenKernel.radialD
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have e : Complex.I * ((k * κ : ℝ) : ℂ) * (r : ℂ) = Complex.I * (κ : ℂ) * ((k * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e]
  push_cast
  generalize Complex.exp (Complex.I * (κ : ℂ) * ((k : ℂ) * (r : ℂ))) = E
  field_simp
  ring

theorem radialDD_scale (κ k r : ℝ) (hk : 0 < k) (hr : r ≠ 0) :
    GreenKernel.radialDD (k * κ) r = (k : ℂ) ^ 3 * GreenKernel.radialDD κ (k * r) := by
  unfold GreenKernel.radialDD
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have e : Complex.I * ((k * κ : ℝ) : ℂ) * (r : ℂ) = Complex.I * (κ : ℂ) * ((k * r : ℝ) : ℂ) := by
    push_cast
    ring
  rw [e]
  push_cast
  generalize Complex.exp (Complex.I * (κ : ℂ) * ((k : ℂ) * (r : ℂ))) = E
  field_simp
  ring

/-! ### The kernels -/

theorem norm_smul_pos (k : ℝ) (hk : 0 < k) (x : Space) : ‖k • x‖ = k * ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg hk.le]

theorem smul_coord (k : ℝ) (x : Space) (i : Fin 3) : (k • x) i = k * x i := rfl

theorem phi_scale_gen (κ k : ℝ) (hk : 0 < k) (x : Space) :
    GreenKernel.phi (k * κ) x = (k : ℂ) * GreenKernel.phi κ (k • x) := by
  unfold GreenKernel.phi
  rw [norm_smul_pos k hk x, radial_scale κ k ‖x‖ hk]
  ring

/-- **`phi_scale`.**  `e^{ik|x|}/(4π|x|) = k · e^{i|kx|}/(4π|kx|)`; also at the origin, where both sides vanish. -/
theorem phi_scale (k : ℝ) (hk : 0 < k) (x : Space) :
    GreenKernel.phi k x = (k : ℂ) * GreenKernel.phi 1 (k • x) := by
  simpa using phi_scale_gen 1 k hk x

theorem phiGradient_scale_gen (κ k : ℝ) (hk : 0 < k) (x : Space) (j : Fin 3) :
    GreenKernel.phiGradient (k * κ) x j = (k : ℂ) ^ 2 * GreenKernel.phiGradient κ (k • x) j := by
  by_cases hx : x = 0
  · subst hx
    simp [GreenKernel.phiGradient]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hkr : (k : ℝ) ≠ 0 := hk.ne'
  unfold GreenKernel.phiGradient
  rw [norm_smul_pos k hk x, radialD_scale κ k ‖x‖ hk hr, smul_coord,
    show k * x j / (k * ‖x‖) = x j / ‖x‖ from mul_div_mul_left _ _ hkr]
  ring

theorem phiGradient_scale (k : ℝ) (hk : 0 < k) (x : Space) (j : Fin 3) :
    GreenKernel.phiGradient k x j = (k : ℂ) ^ 2 * GreenKernel.phiGradient 1 (k • x) j := by
  simpa using phiGradient_scale_gen 1 k hk x j

theorem hess_inner (A B a c r d k : ℂ) (hk : k ≠ 0) (hr : r ≠ 0) :
    k ^ 3 * A * a * c / r ^ 2 + k ^ 2 * B * (d / r - a * c / r ^ 3) =
      k ^ 3 * (A * (k * a) * (k * c) / (k * r) ^ 2 + B * (d / (k * r) - (k * a) * (k * c) / (k * r) ^ 3)) := by
  field_simp
  ring

theorem hess_alg (A B a c r d k p : ℂ) (hk : k ≠ 0) (hr : r ≠ 0) :
    (k ^ 3 * A * a * c / r ^ 2 + k ^ 2 * B * (d / r - a * c / r ^ 3)) / (4 * p) =
      k ^ 3 * ((A * (k * a) * (k * c) / (k * r) ^ 2 + B * (d / (k * r) - (k * a) * (k * c) / (k * r) ^ 3)) /
        (4 * p)) := by
  rw [hess_inner A B a c r d k hk hr]
  ring

theorem phiHessian_scale_gen (κ k : ℝ) (hk : 0 < k) (x : Space) (i j : Fin 3) :
    GreenKernel.phiHessian (k * κ) x i j = (k : ℂ) ^ 3 * GreenKernel.phiHessian κ (k • x) i j := by
  by_cases hx : x = 0
  · subst hx
    simp [GreenKernel.phiHessian]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hr
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold GreenKernel.phiHessian
  rw [norm_smul_pos k hk x, radialDD_scale κ k ‖x‖ hk hr, radialD_scale κ k ‖x‖ hk hr, smul_coord,
    smul_coord]
  push_cast
  exact hess_alg _ _ _ _ _ _ _ _ hkc hrc

/-- **`phiHessian_scale`.**  The Hessian of the frequency-`k` kernel is `k³` times the Hessian of the frequency-one
kernel at the dilated point. -/
theorem phiHessian_scale (k : ℝ) (hk : 0 < k) (x : Space) (i j : Fin 3) :
    GreenKernel.phiHessian k x i j = (k : ℂ) ^ 3 * GreenKernel.phiHessian 1 (k • x) i j := by
  simpa using phiHessian_scale_gen 1 k hk x i j

/-- The static Hessian is homogeneous of degree `-3`. -/
theorem phiHessian_zero_scale (k : ℝ) (hk : 0 < k) (x : Space) (i j : Fin 3) :
    GreenKernel.phiHessian 0 x i j = (k : ℂ) ^ 3 * GreenKernel.phiHessian 0 (k • x) i j := by
  simpa using phiHessian_scale_gen 0 k hk x i j

theorem dyadic_scale_gen (κ k : ℝ) (hk : 0 < k) (x : Space) (i j : Fin 3) :
    DyadicKernel.dyadic (k * κ) x i j = (k : ℂ) ^ 3 * DyadicKernel.dyadic κ (k • x) i j := by
  unfold DyadicKernel.dyadic
  rw [phiHessian_scale_gen κ k hk x i j, phi_scale_gen κ k hk x]
  push_cast
  ring

/-- **`dyadic_scale`.** -/
theorem dyadic_scale (k : ℝ) (hk : 0 < k) (x : Space) (i j : Fin 3) :
    DyadicKernel.dyadic k x i j = (k : ℂ) ^ 3 * DyadicKernel.dyadic 1 (k • x) i j := by
  simpa using dyadic_scale_gen 1 k hk x i j

/-- **`remainder_scale`.** -/
theorem remainder_scale (k : ℝ) (hk : 0 < k) (x : Space) (i j : Fin 3) :
    DyadicKernel.remainder k x i j = (k : ℂ) ^ 3 * DyadicKernel.remainder 1 (k • x) i j := by
  unfold DyadicKernel.remainder
  rw [dyadic_scale k hk x i j, phiHessian_zero_scale k hk x i j]
  ring

/-! ### The dilated source -/

theorem dilated_integrable (k : ℝ) (hk : 0 < k) (ρ : Space → ℂ) (hρ : Integrable ρ volume) :
    Integrable (fun y => (k : ℂ) * ρ (k • y)) volume :=
  (hρ.comp_smul hk.ne').const_mul (k : ℂ)

theorem dilated_hasCompactSupport (k : ℝ) (hk : 0 < k) (ρ : Space → ℂ) (hρ : HasCompactSupport ρ) :
    HasCompactSupport (fun y => (k : ℂ) * ρ (k • y)) :=
  (hρ.comp_smul hk.ne').mul_left

/-! ### The responses -/

/-- **Change of variables in the response.**  If the kernel `q` is `c` times the dilation of the kernel `q1`, the
response to the dilated source `y ↦ k ρ (k y)` at `x` is `k c k⁻³` times the response of `q1` to `ρ` at `k x`. -/
theorem response_dilate (k : ℝ) (hk : 0 < k) (q q1 : Space → ℂ) (c : ℂ) (hq : ∀ z, q z = c * q1 (k • z))
    (ρ : Space → ℂ) (x : Space) :
    KernelConvolution.response q (fun y => (k : ℂ) * ρ (k • y)) x =
      (k : ℂ) * c * ((k : ℂ) ^ 3)⁻¹ * KernelConvolution.response q1 ρ (k • x) := by
  unfold KernelConvolution.response
  have h1 : (fun y => ((k : ℂ) * ρ (k • y)) * q (x - y)) =
      fun y => ((k : ℂ) * c) * (fun y' => ρ y' * q1 (k • x - y')) (k • y) := by
    funext y
    rw [hq, smul_sub]
    ring
  rw [h1, integral_const_mul, Measure.integral_comp_smul volume (fun y' => ρ y' * q1 (k • x - y')) k]
  rw [finrank_euclideanSpace_fin, abs_of_pos (inv_pos.mpr (pow_pos hk 3)), Complex.real_smul]
  push_cast
  ring

/-- **`response_scale`.**  The remainder response to the dilated source. -/
theorem response_scale (k : ℝ) (hk : 0 < k) (ρ : Space → ℂ) (i j : Fin 3) (x : Space) :
    KernelConvolution.response (fun z => DyadicKernel.remainder k z i j) (fun y => (k : ℂ) * ρ (k • y)) x =
      (k : ℂ) * KernelConvolution.response (fun z => DyadicKernel.remainder 1 z i j) ρ (k • x) := by
  rw [response_dilate k hk (fun z => DyadicKernel.remainder k z i j) (fun z => DyadicKernel.remainder 1 z i j)
    ((k : ℂ) ^ 3) (fun z => remainder_scale k hk z i j) ρ x]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- The gradient-kernel response to the dilated source is the response to the source at the dilated point
(the factor `k²` of the kernel, `k⁻³` of the Jacobian and `k` of the source cancel). -/
theorem gradient_response_scale (k : ℝ) (hk : 0 < k) (ρ : Space → ℂ) (l : Fin 3) (x : Space) :
    KernelConvolution.response (fun z => GreenKernel.phiGradient k z l) (fun y => (k : ℂ) * ρ (k • y)) x =
      KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z l) ρ (k • x) := by
  rw [response_dilate k hk (fun z => GreenKernel.phiGradient k z l) (fun z => GreenKernel.phiGradient 1 z l)
    ((k : ℂ) ^ 2) (fun z => phiGradient_scale k hk z l) ρ x]
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
  ring

/-- **`magnetic_scale`.**  The magnetic response to the dilated source. -/
theorem magnetic_scale (k : ℝ) (hk : 0 < k) (ρ : Fin 3 → Space → ℂ) (x : Space) (i : Fin 3) :
    MagneticResponse.magnetic k (fun j y => (k : ℂ) * ρ j (k • y)) x i =
      (k : ℂ) * MagneticResponse.magnetic 1 ρ (k • x) i := by
  unfold MagneticResponse.magnetic
  rw [gradient_response_scale k hk (ρ (OQ14.WeakCurl.previous i)) (OQ14.WeakCurl.next i) x,
    gradient_response_scale k hk (ρ (OQ14.WeakCurl.next i)) (OQ14.WeakCurl.previous i) x]
  push_cast
  ring

/-- **`electric_remainder_scale`.**  The remainder part of the electric field response
(`FieldResponse.electric k F ρ x i = physicalCoordinate (newtonOperator F) i x + ∑ j, response (remainder k · i j) (ρ j) x`)
for the dilated source. -/
theorem electric_remainder_scale (k : ℝ) (hk : 0 < k) (ρ : Fin 3 → Space → ℂ) (x : Space) (i : Fin 3) :
    ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder k z i j)
        ((fun j y => (k : ℂ) * ρ j (k • y)) j) x =
      (k : ℂ) * ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder 1 z i j) (ρ j) (k • x) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => response_scale k hk (ρ j) i j x)

end OQ14.DilationKernels

#print axioms OQ14.DilationKernels.radial_scale
#print axioms OQ14.DilationKernels.radialD_scale
#print axioms OQ14.DilationKernels.radialDD_scale
#print axioms OQ14.DilationKernels.norm_smul_pos
#print axioms OQ14.DilationKernels.smul_coord
#print axioms OQ14.DilationKernels.phi_scale_gen
#print axioms OQ14.DilationKernels.phi_scale
#print axioms OQ14.DilationKernels.phiGradient_scale_gen
#print axioms OQ14.DilationKernels.phiGradient_scale
#print axioms OQ14.DilationKernels.hess_inner
#print axioms OQ14.DilationKernels.hess_alg
#print axioms OQ14.DilationKernels.phiHessian_scale_gen
#print axioms OQ14.DilationKernels.phiHessian_scale
#print axioms OQ14.DilationKernels.phiHessian_zero_scale
#print axioms OQ14.DilationKernels.dyadic_scale_gen
#print axioms OQ14.DilationKernels.dyadic_scale
#print axioms OQ14.DilationKernels.remainder_scale
#print axioms OQ14.DilationKernels.dilated_integrable
#print axioms OQ14.DilationKernels.dilated_hasCompactSupport
#print axioms OQ14.DilationKernels.response_dilate
#print axioms OQ14.DilationKernels.response_scale
#print axioms OQ14.DilationKernels.gradient_response_scale
#print axioms OQ14.DilationKernels.magnetic_scale
#print axioms OQ14.DilationKernels.electric_remainder_scale
