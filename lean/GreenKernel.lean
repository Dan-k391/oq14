import Maxwell
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp

/-!
# The outgoing scalar Helmholtz kernel away from its source

Actual real Frechet derivatives are used. The distributional delta at
the origin, convolution mapping properties and radiation solvability are
separate obligations; no such conclusions are assumptions here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.GreenKernel

open OQ14.Maxwell
open scoped InnerProductSpace

def radial (k r : ℝ) : ℂ := Complex.exp (Complex.I * k * r) / (r : ℂ)
def radialD (k r : ℝ) : ℂ :=
  Complex.exp (Complex.I * k * r) * (Complex.I * k / r - 1 / (r : ℂ)^2)
def radialDD (k r : ℝ) : ℂ :=
  Complex.exp (Complex.I * k * r) *
    ((Complex.I * k)^2 / r - 2 * (Complex.I * k) / (r : ℂ)^2 + 2 / (r : ℂ)^3)

theorem complex_radius_hasDerivAt (r : ℝ) :
    HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
  simpa using Complex.ofRealCLM.hasFDerivAt.hasDerivAt (x := r)

theorem radial_hasDerivAt (k r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (radial k) (radialD k r) r := by
  have hc := complex_radius_hasDerivAt r
  have he := (hc.const_mul (Complex.I * k)).cexp
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  convert he.div hc hrc using 1
  dsimp [radialD]
  field_simp [hrc]
  ring

theorem radialD_hasDerivAt (k r : ℝ) (hr : r ≠ 0) :
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

theorem radial_helmholtz (k r : ℝ) (hr : r ≠ 0) :
    radialDD k r + 2 / (r : ℂ) * radialD k r + (k : ℂ)^2 * radial k r = 0 := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  unfold radialDD radialD radial
  field_simp [hrc]
  ring_nf
  norm_num [Complex.I_sq]

theorem norm_partial (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    fderiv ℝ (fun y : Space => ‖y‖) x (basis i) = x i / ‖x‖ := by
  have hn := (differentiableAt_id.norm ℝ hx).hasFDerivAt
  have hs := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have he := (hn.mul hn).unique (by simpa only [pow_two] using hs)
  have hv := congrArg (fun L : Space →L[ℝ] ℝ => L (basis i)) he
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, innerSL_apply] at hv
  simp only [id_eq, basis, EuclideanSpace.inner_single_right, one_mul,
    smul_eq_mul] at hv
  apply (eq_div_iff hr).2
  simp only [basis]
  simp at hv
  nlinarith

theorem radial_composition_partial (f : ℝ → ℂ) (df : ℂ)
    (x : Space) (hx : x ≠ 0) (hf : HasDerivAt f df ‖x‖) (i : Fin 3) :
    dcoord (fun y => f ‖y‖) x i = df * (x i / ‖x‖ : ℝ) := by
  have hn := (differentiableAt_id.norm ℝ hx).hasFDerivAt
  have hh := (hf.hasFDerivAt.comp x hn).fderiv
  simp only [Function.comp_def, id_eq] at hh
  unfold dcoord
  rw [hh]
  simp [norm_partial x hx i, smul_eq_mul, mul_comm]

def phi (k : ℝ) (x : Space) : ℂ := radial k ‖x‖ / (4 * Real.pi)
def phiGradient (k : ℝ) (x : Space) (j : Fin 3) : ℂ :=
  radialD k ‖x‖ * (x j / ‖x‖ : ℝ) / (4 * Real.pi)

theorem phi_partial (k : ℝ) (x : Space) (hx : x ≠ 0) (j : Fin 3) :
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

def unitCoordinate (j : Fin 3) (x : Space) : ℂ := (x j / ‖x‖ : ℝ)

theorem unitCoordinate_differentiableAt (j : Fin 3) (x : Space) (hx : x ≠ 0) :
    DifferentiableAt ℝ (unitCoordinate j) x := by
  have hn : HasFDerivAt (fun y : Space => ‖y‖)
      (fderiv ℝ (fun y : Space => ‖y‖) x) x :=
    (differentiableAt_id.norm ℝ hx).hasFDerivAt
  have hc := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hi := (hasDerivAt_inv (norm_ne_zero_iff.mpr hx)).hasFDerivAt.comp x hn
  change DifferentiableAt ℝ (fun y : Space => ((y j / ‖y‖ : ℝ) : ℂ)) x
  simpa [unitCoordinate, Function.comp_def, div_eq_mul_inv] using
    (Complex.ofRealCLM.hasFDerivAt.comp x (hc.mul hi)).differentiableAt

theorem unitCoordinate_partial (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    dcoord (unitCoordinate j) x i =
      (if i = j then 1 else 0 : ℂ) / (‖x‖ : ℂ) -
        (x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^3 := by
  have hn : HasFDerivAt (fun y : Space => ‖y‖)
      (fderiv ℝ (fun y : Space => ‖y‖) x) x :=
    (differentiableAt_id.norm ℝ hx).hasFDerivAt
  have hc := (EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt (x := x)
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hr
  have hi := (hasDerivAt_inv hr).hasFDerivAt.comp x hn
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x (hc.mul hi)
  have he := hd.fderiv
  have hfun : (Complex.ofRealCLM ∘ fun y : Space =>
      (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y * ((fun t : ℝ => t⁻¹) ∘ norm) y) =
      unitCoordinate j := by
    funext y
    simp [unitCoordinate, Function.comp_def, div_eq_mul_inv]
  rw [hfun] at he
  unfold dcoord
  rw [he]
  have hnp : fderiv ℝ (fun y : Space => ‖y‖) x (EuclideanSpace.single i 1) =
      x i / ‖x‖ := norm_partial x hx i
  simp [ContinuousLinearMap.comp_apply, hnp,
    basis, EuclideanSpace.single_apply, eq_comm]
  split_ifs <;> push_cast <;> field_simp [hrc] <;> ring

def phiHessian (k : ℝ) (x : Space) (i j : Fin 3) : ℂ :=
  (radialDD k ‖x‖ * (x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^2 +
    radialD k ‖x‖ * ((if i = j then 1 else 0 : ℂ) / (‖x‖ : ℂ) -
      (x i : ℂ) * (x j : ℂ) / (‖x‖ : ℂ)^3)) / (4 * Real.pi)

theorem phiGradient_partial (k : ℝ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
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

theorem phi_second_partial (k : ℝ) (x : Space) (hx : x ≠ 0) (i j : Fin 3) :
    dcoord (fun y => dcoord (phi k) y j) x i = phiHessian k x i j := by
  have he : (fun y => dcoord (phi k) y j) =ᶠ[nhds x] (fun y => phiGradient k y j) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact phi_partial k y hy j
  change (fderiv ℝ (fun y => dcoord (phi k) y j) x) (basis i) = _
  rw [he.fderiv_eq]
  exact phiGradient_partial k x hx i j

theorem coordinate_squares (x : Space) :
    (x 0 : ℂ)^2 + (x 1 : ℂ)^2 + (x 2 : ℂ)^2 = (‖x‖ : ℂ)^2 := by
  have h : (x 0)^2 + (x 1)^2 + (x 2)^2 = ‖x‖^2 := by
    simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using
      (PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x).symm
  exact_mod_cast h

theorem phiHessian_trace (k : ℝ) (x : Space) (hx : x ≠ 0) :
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

/-- The actual three-dimensional scalar Helmholtz equation away from the source. -/
theorem phi_helmholtz (k : ℝ) (x : Space) (hx : x ≠ 0) :
    divergence (gradient (phi k)) x + (k : ℂ)^2 * phi k x = 0 := by
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have ho := radial_helmholtz k ‖x‖ hr
  unfold divergence pd gradient
  rw [phi_second_partial k x hx, phi_second_partial k x hx, phi_second_partial k x hx,
    phiHessian_trace k x hx]
  unfold phi
  convert congrArg (fun z : ℂ => z / (4 * Real.pi)) ho using 1 <;> ring

theorem phi_contDiffAt (k : ℝ) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ ⊤ (phi k) x := by
  have hn : ContDiffAt ℝ ⊤ (fun y : Space => ‖y‖) x := contDiffAt_norm ℝ hx
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hn
  have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have hh := ((((contDiffAt_const (c := Complex.I * k)).mul hc).cexp).mul (hc.inv hr)).mul
    (contDiffAt_const (c := (4 * (Real.pi : ℂ))⁻¹))
  change ContDiffAt ℝ ⊤ (fun y : Space => phi k y) x
  simpa [phi, radial, div_eq_mul_inv, Function.comp_def] using hh

theorem radial_norm (k r : ℝ) : ‖radial k r‖ = 1 / |r| := by
  simp [radial, norm_div, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem radial_sommerfeld_remainder (k r : ℝ) (hr : r ≠ 0) :
    (r : ℂ) * (radialD k r - Complex.I * k * radial k r) =
      -Complex.exp (Complex.I * k * r) / r := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  unfold radialD radial
  field_simp [hrc]
  ring

/-- The outgoing radial solution satisfies the Sommerfeld limit for real k. -/
theorem radial_sommerfeld (k : ℝ) :
    Filter.Tendsto (fun r : ℝ => (r : ℂ) * (radialD k r - Complex.I * k * radial k r))
      Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have he : (fun r : ℝ => ‖(r : ℂ) * (radialD k r - Complex.I * k * radial k r)‖)
      =ᶠ[Filter.atTop] (fun r : ℝ => r⁻¹) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
    rw [radial_sommerfeld_remainder k r hr.ne']
    simp [norm_div, Complex.norm_exp, Complex.mul_re, Complex.mul_im, abs_of_pos hr]
  exact tendsto_inv_atTop_zero.congr' he.symm

end OQ14.GreenKernel

#print axioms OQ14.GreenKernel.radial_hasDerivAt
#print axioms OQ14.GreenKernel.radialD_hasDerivAt
#print axioms OQ14.GreenKernel.radial_helmholtz
#print axioms OQ14.GreenKernel.norm_partial
#print axioms OQ14.GreenKernel.radial_composition_partial
#print axioms OQ14.GreenKernel.phi_partial
#print axioms OQ14.GreenKernel.unitCoordinate_differentiableAt
#print axioms OQ14.GreenKernel.unitCoordinate_partial
#print axioms OQ14.GreenKernel.phiGradient_partial
#print axioms OQ14.GreenKernel.phi_second_partial
#print axioms OQ14.GreenKernel.coordinate_squares
#print axioms OQ14.GreenKernel.phiHessian_trace
#print axioms OQ14.GreenKernel.phi_helmholtz
#print axioms OQ14.GreenKernel.phi_contDiffAt
#print axioms OQ14.GreenKernel.radial_norm
#print axioms OQ14.GreenKernel.radial_sommerfeld_remainder
#print axioms OQ14.GreenKernel.radial_sommerfeld
