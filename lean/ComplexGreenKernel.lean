import GreenKernel

/-! # The physical Helmholtz kernel at complex frequency

The scalar kernel, its gradient and Hessian retain their actual real spatial
Frechet derivative meaning for every complex frequency. Restriction to real
frequency agrees exactly with the existing physical kernels.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.ComplexGreenKernel

open OQ14.Maxwell OQ14.GreenKernel
open scoped InnerProductSpace

def radial (k : ℂ) (r : ℝ) : ℂ := Complex.exp (Complex.I * k * r) / (r : ℂ)

def radialD (k : ℂ) (r : ℝ) : ℂ :=
  Complex.exp (Complex.I * k * r) * (Complex.I * k / r - 1 / (r : ℂ)^2)

def radialDD (k : ℂ) (r : ℝ) : ℂ :=
  Complex.exp (Complex.I * k * r) *
    ((Complex.I * k)^2 / r - 2 * (Complex.I * k) / (r : ℂ)^2 + 2 / (r : ℂ)^3)

theorem radial_hasDerivAt (k : ℂ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (radial k) (radialD k r) r := by
  have hc := complex_radius_hasDerivAt r
  have he := (hc.const_mul (Complex.I * k)).cexp
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  convert he.div hc hrc using 1
  dsimp [radialD]
  field_simp [hrc]
  ring

theorem radialD_hasDerivAt (k : ℂ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (radialD k) (radialDD k r) r := by
  have hc := complex_radius_hasDerivAt r
  have he := (hc.const_mul (Complex.I * k)).cexp
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have h1 := (hasDerivAt_const r (Complex.I * k)).div hc hrc
  have hsq : HasDerivAt (fun t : ℝ => (t : ℂ)^2) (2 * (r : ℂ)) r := by
    convert hc.mul hc using 1 <;> ring
  have h2 := (hasDerivAt_const r (1 : ℂ)).div hsq (pow_ne_zero 2 hrc)
  convert he.mul (h1.sub h2) using 1
  dsimp [radialDD]
  field_simp [hrc]
  ring

theorem radial_helmholtz (k : ℂ) (r : ℝ) (hr : r ≠ 0) :
    radialDD k r + 2 / (r : ℂ) * radialD k r + k^2 * radial k r = 0 := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  unfold radialDD radialD radial
  field_simp [hrc]
  ring_nf
  norm_num [Complex.I_sq]

def phi (k : ℂ) (x : Space) : ℂ := radial k ‖x‖ / (4 * Real.pi)

def phiGradient (k : ℂ) (x : Space) (j : Fin 3) : ℂ :=
  radialD k ‖x‖ * (x j / ‖x‖ : ℝ) / (4 * Real.pi)

theorem phi_partial (k : ℂ) (x : Space) (hx : x ≠ 0) (j : Fin 3) :
    dcoord (phi k) x j = phiGradient k x j := by
  have hr := norm_ne_zero_iff.mpr hx
  have hd := radial_hasDerivAt k ‖x‖ hr
  have hcomp := hd.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt
  have hdiff : DifferentiableAt ℝ (fun y : Space => radial k ‖y‖) x :=
    hcomp.differentiableAt
  have hp := radial_composition_partial (radial k) (radialD k ‖x‖) x hx hd j
  have heq : phi k = fun y => (1 / (4 * Real.pi) : ℂ) * radial k ‖y‖ := by
    funext y
    simp [phi, div_eq_mul_inv, mul_comm]
  rw [heq, partial_const_mul hdiff, hp]
  simp [phiGradient, div_eq_mul_inv, mul_comm]

def phiHessian (k : ℂ) (x : Space) (i j : Fin 3) : ℂ :=
  (radialDD k ‖x‖ * (x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2 +
    radialD k ‖x‖ * ((if i = j then 1 else 0 : ℂ) / (‖x‖ : ℂ) -
      (x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^3)) / (4 * Real.pi)

theorem phiGradient_partial (k : ℂ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    dcoord (fun y => phiGradient k y j) x i = phiHessian k x i j := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hr
  have hd := radialD_hasDerivAt k ‖x‖ hr
  have hdiff : DifferentiableAt ℝ (fun y : Space => radialD k ‖y‖) x :=
    (hd.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  have hu := unitCoordinate_differentiableAt j x hx
  have heq : (fun y => phiGradient k y j) =
      fun y => (1 / (4 * Real.pi) : ℂ) * (radialD k ‖y‖ * unitCoordinate j y) := by
    funext y
    simp [phiGradient, unitCoordinate, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [heq, partial_const_mul (hdiff.mul hu), partial_mul hdiff hu,
    unitCoordinate_partial i j x hx, radial_composition_partial _ _ x hx hd i]
  unfold unitCoordinate phiHessian
  push_cast
  field_simp [hrc]
  ring

theorem phi_second_partial (k : ℂ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    dcoord (fun y => dcoord (phi k) y j) x i = phiHessian k x i j := by
  have he : (fun y => dcoord (phi k) y j) =ᶠ[nhds x] (fun y => phiGradient k y j) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact phi_partial k y hy j
  change (fderiv ℝ (fun y => dcoord (phi k) y j) x) (basis i) = _
  rw [he.fderiv_eq]
  exact phiGradient_partial k x hx i j

theorem phiHessian_trace (k : ℂ) (x : Space) (hx : x ≠ 0) :
    phiHessian k x 0 0 + phiHessian k x 1 1 + phiHessian k x 2 2 =
      (radialDD k ‖x‖ + 2 / (‖x‖ : ℂ) * radialD k ‖x‖) / (4 * Real.pi) := by
  have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have hs := coordinate_squares x
  calc
    _ = (radialDD k ‖x‖ * ((x 0 : ℂ)^2 + (x 1 : ℂ)^2 + (x 2 : ℂ)^2) /
          (‖x‖ : ℂ)^2 + radialD k ‖x‖ * (3 / (‖x‖ : ℂ) -
          ((x 0 : ℂ)^2 + (x 1 : ℂ)^2 + (x 2 : ℂ)^2) / (‖x‖ : ℂ)^3)) /
          (4 * Real.pi) := by simp only [phiHessian, ite_true]; ring
    _ = _ := by
      rw [hs]
      congr 1
      field_simp [hr]
      ring

theorem phi_helmholtz (k : ℂ) (x : Space) (hx : x ≠ 0) :
    divergence (gradient (phi k)) x + k^2 * phi k x = 0 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ho := radial_helmholtz k ‖x‖ hr
  unfold divergence pd gradient
  rw [phi_second_partial k x hx, phi_second_partial k x hx, phi_second_partial k x hx,
    phiHessian_trace k x hx]
  unfold phi
  convert congrArg (fun z : ℂ => z / (4 * Real.pi)) ho using 1 <;> ring

theorem phi_contDiffAt (k : ℂ) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ ⊤ (phi k) x := by
  have hn : ContDiffAt ℝ ⊤ (fun y : Space => ‖y‖) x := contDiffAt_norm ℝ hx
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hn
  have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have hh := ((((contDiffAt_const (c := Complex.I * k)).mul hc).cexp).mul (hc.inv hr)).mul
    (contDiffAt_const (c := (4 * (Real.pi : ℂ))⁻¹))
  change ContDiffAt ℝ ⊤ (fun y : Space => phi k y) x
  simpa [phi, radial, div_eq_mul_inv, Function.comp_def] using hh

theorem radial_ofReal (k r : ℝ) : radial (k : ℂ) r = GreenKernel.radial k r := rfl

theorem radialD_ofReal (k r : ℝ) : radialD (k : ℂ) r = GreenKernel.radialD k r := rfl

theorem radialDD_ofReal (k r : ℝ) : radialDD (k : ℂ) r = GreenKernel.radialDD k r := rfl

theorem phi_ofReal (k : ℝ) (x : Space) : phi (k : ℂ) x = GreenKernel.phi k x := rfl

theorem phiGradient_ofReal (k : ℝ) (x : Space) (j : Fin 3) :
    phiGradient (k : ℂ) x j = GreenKernel.phiGradient k x j := rfl

theorem phiHessian_ofReal (k : ℝ) (x : Space) (i j : Fin 3) :
    phiHessian (k : ℂ) x i j = GreenKernel.phiHessian k x i j := rfl

end OQ14.ComplexGreenKernel

#print axioms OQ14.ComplexGreenKernel.radial_hasDerivAt
#print axioms OQ14.ComplexGreenKernel.radialD_hasDerivAt
#print axioms OQ14.ComplexGreenKernel.radial_helmholtz
#print axioms OQ14.ComplexGreenKernel.phi_partial
#print axioms OQ14.ComplexGreenKernel.phiGradient_partial
#print axioms OQ14.ComplexGreenKernel.phi_second_partial
#print axioms OQ14.ComplexGreenKernel.phiHessian_trace
#print axioms OQ14.ComplexGreenKernel.phi_helmholtz
#print axioms OQ14.ComplexGreenKernel.phi_contDiffAt
#print axioms OQ14.ComplexGreenKernel.radial_ofReal
#print axioms OQ14.ComplexGreenKernel.radialD_ofReal
#print axioms OQ14.ComplexGreenKernel.radialDD_ofReal
#print axioms OQ14.ComplexGreenKernel.phi_ofReal
#print axioms OQ14.ComplexGreenKernel.phiGradient_ofReal
#print axioms OQ14.ComplexGreenKernel.phiHessian_ofReal
