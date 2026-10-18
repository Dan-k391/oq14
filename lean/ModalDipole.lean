import ModalMatching
import GreenKernel

/-!
# Actual complex-frequency dipole Maxwell fields

The curls are the actual real Frechet coordinate curls on Euclidean space.
Radial ODEs are converted to fields before any interface claim is made.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.ModalDipole

open Complex OQ14.Maxwell OQ14.GreenKernel OQ14.ModalAlgebra OQ14.ModalWronskian

def axisField (A B : ℝ → ℂ) : Field := fun x =>
  ![B ‖x‖ * (x 2 : ℂ) * (x 0 : ℂ),
    B ‖x‖ * (x 2 : ℂ) * (x 1 : ℂ),
    A ‖x‖ + B ‖x‖ * (x 2 : ℂ) * (x 2 : ℂ)]

def swirlField (C : ℝ → ℂ) : Field := fun x =>
  ![C ‖x‖ * (x 1 : ℂ), -C ‖x‖ * (x 0 : ℂ), 0]

theorem coordinate_partial (x : Space) (i j : Fin 3) :
    dcoord (fun y : Space => (y j : ℂ)) x i = if i = j then 1 else 0 := by
  change (fderiv ℝ (coordinate j) x) (basis i) = _
  rw [(coordinate j).hasFDerivAt.fderiv]
  simp [coordinate, basis, EuclideanSpace.single_apply, eq_comm]
  split_ifs <;> norm_num

theorem coordinate_differentiableAt (x : Space) (j : Fin 3) :
    DifferentiableAt ℝ (fun y : Space => (y j : ℂ)) x := by
  exact (coordinate j).differentiableAt

theorem radial_coordinate_partial (F : ℝ → ℂ) (dF : ℂ)
    (x : Space) (hx : x ≠ 0) (hF : HasDerivAt F dF ‖x‖) (i j : Fin 3) :
    dcoord (fun y : Space => F ‖y‖ * (y j : ℂ)) x i =
      F ‖x‖ * (if i = j then 1 else 0 : ℂ) + (x j : ℂ) * dF * (x i / ‖x‖ : ℝ) := by
  have hf := (hF.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  change DifferentiableAt ℝ (fun y : Space => F ‖y‖) x at hf
  rw [partial_mul hf (coordinate_differentiableAt x j), coordinate_partial,
    radial_composition_partial F dF x hx hF]
  ring

theorem radial_two_coordinates_partial (F : ℝ → ℂ) (dF : ℂ)
    (x : Space) (hx : x ≠ 0) (hF : HasDerivAt F dF ‖x‖) (i j m : Fin 3) :
    dcoord (fun y : Space => F ‖y‖ * (y j : ℂ) * (y m : ℂ)) x i =
      F ‖x‖ * (x j : ℂ) * (if i = m then 1 else 0 : ℂ) +
        (x m : ℂ) * (F ‖x‖ * (if i = j then 1 else 0 : ℂ) +
          (x j : ℂ) * dF * (x i / ‖x‖ : ℝ)) := by
  have hf := (hF.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  change DifferentiableAt ℝ (fun y : Space => F ‖y‖) x at hf
  rw [partial_mul (hf.mul (coordinate_differentiableAt x j)) (coordinate_differentiableAt x m),
    coordinate_partial, radial_coordinate_partial F dF x hx hF]

theorem axisField_curl (A B : ℝ → ℂ) (dA dB : ℂ)
    (x : Space) (hx : x ≠ 0) (hA : HasDerivAt A dA ‖x‖) (hB : HasDerivAt B dB ‖x‖) :
    curl (axisField A B) x =
      ![(dA / (‖x‖ : ℂ) - B ‖x‖) * (x 1 : ℂ),
        -(dA / (‖x‖ : ℂ) - B ‖x‖) * (x 0 : ℂ), 0] := by
  have ha := (hA.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  have hb := (hB.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  change DifferentiableAt ℝ (fun y : Space => A ‖y‖) x at ha
  change DifferentiableAt ℝ (fun y : Space => B ‖y‖) x at hb
  have hbb := (hb.mul (coordinate_differentiableAt x 2)).mul (coordinate_differentiableAt x 2)
  ext j
  fin_cases j
  · change dcoord (fun y => A ‖y‖ + B ‖y‖ * (y 2 : ℂ) * (y 2 : ℂ)) x 1 -
        dcoord (fun y => B ‖y‖ * (y 2 : ℂ) * (y 1 : ℂ)) x 2 = _
    rw [partial_add ha hbb, radial_composition_partial A dA x hx hA,
      radial_two_coordinates_partial B dB x hx hB, radial_two_coordinates_partial B dB x hx hB]
    simp only [ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
    push_cast
    ring
  · change dcoord (fun y => B ‖y‖ * (y 2 : ℂ) * (y 0 : ℂ)) x 2 -
        dcoord (fun y => A ‖y‖ + B ‖y‖ * (y 2 : ℂ) * (y 2 : ℂ)) x 0 = _
    rw [radial_two_coordinates_partial B dB x hx hB, partial_add ha hbb,
      radial_composition_partial A dA x hx hA, radial_two_coordinates_partial B dB x hx hB]
    simp only [ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
    push_cast
    ring
  · change dcoord (fun y => B ‖y‖ * (y 2 : ℂ) * (y 1 : ℂ)) x 0 -
        dcoord (fun y => B ‖y‖ * (y 2 : ℂ) * (y 0 : ℂ)) x 1 = 0
    rw [radial_two_coordinates_partial B dB x hx hB, radial_two_coordinates_partial B dB x hx hB]
    simp only [ite_true, ite_false, mul_one, mul_zero, add_zero, zero_add]
    push_cast
    ring

theorem swirlField_curl (C : ℝ → ℂ) (dC : ℂ)
    (x : Space) (hx : x ≠ 0) (hC : HasDerivAt C dC ‖x‖) :
    curl (swirlField C) x =
      ![dC / (‖x‖ : ℂ) * (x 2 : ℂ) * (x 0 : ℂ),
        dC / (‖x‖ : ℂ) * (x 2 : ℂ) * (x 1 : ℂ),
        dC / (‖x‖ : ℂ) * (x 2 : ℂ)^2 - ((‖x‖ : ℂ) * dC + 2 * C ‖x‖)] := by
  have hc := (hC.hasFDerivAt.comp x (differentiableAt_id.norm ℝ hx).hasFDerivAt).differentiableAt
  change DifferentiableAt ℝ (fun y : Space => C ‖y‖) x at hc
  have hneg (i : Fin 3) :
      dcoord (fun y : Space => -C ‖y‖ * (y 0 : ℂ)) x i =
        -dcoord (fun y : Space => C ‖y‖ * (y 0 : ℂ)) x i := by
    have heq : (fun y : Space => -C ‖y‖ * (y 0 : ℂ)) =
        fun y : Space => (-1 : ℂ) * (C ‖y‖ * (y 0 : ℂ)) := by funext y; ring
    rw [heq, partial_const_mul (hc.mul (coordinate_differentiableAt x 0))]
    ring
  have hzero (i : Fin 3) : dcoord (fun _ : Space => (0 : ℂ)) x i = 0 := by simp [dcoord]
  ext j
  fin_cases j
  · change dcoord (fun _ : Space => (0 : ℂ)) x 1 -
        dcoord (fun y => -C ‖y‖ * (y 0 : ℂ)) x 2 = _
    rw [hzero, hneg, radial_coordinate_partial C dC x hx hC]
    simp only [ite_false, mul_zero, zero_add, zero_sub, neg_neg]
    push_cast
    ring
  · change dcoord (fun y => C ‖y‖ * (y 1 : ℂ)) x 2 -
        dcoord (fun _ : Space => (0 : ℂ)) x 0 = _
    rw [radial_coordinate_partial C dC x hx hC, hzero]
    simp only [ite_false, mul_zero, zero_add, sub_zero]
    push_cast
    ring
  · change dcoord (fun y => -C ‖y‖ * (y 0 : ℂ)) x 0 -
        dcoord (fun y => C ‖y‖ * (y 1 : ℂ)) x 1 = _
    rw [hneg, radial_coordinate_partial C dC x hx hC, radial_coordinate_partial C dC x hx hC]
    simp only [ite_true, mul_one]
    push_cast
    have hr : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
    field_simp
    have hs := coordinate_squares x
    linear_combination -dC * hs

def electricA (uD : ℝ → ℂ) (r : ℝ) : ℂ := uD r / (r : ℂ)
def electricB (u uD : ℝ → ℂ) (r : ℝ) : ℂ :=
  2 * u r / (r : ℂ)^4 - uD r / (r : ℂ)^3
def magneticC (κ k : ℂ) (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  (I * κ^2 / k) * u r / (r : ℂ)^2

def dipoleE (u uD : ℝ → ℂ) : Field := axisField (electricA uD) (electricB u uD)
def dipoleH (κ k : ℂ) (u : ℝ → ℂ) : Field := swirlField (magneticC κ k u)

def ComplexMaxwellAt (k ε : ℂ) (E H : Field) (x : Space) : Prop :=
  curl E x = (fun j => I * k * H x j) ∧
    curl H x = (fun j => -I * k * ε * E x j)

theorem electricA_hasDerivAt (uD : ℝ → ℂ) (w : ℂ) (r : ℝ) (hr : r ≠ 0)
    (hv : HasDerivAt uD w r) :
    HasDerivAt (electricA uD) (w / (r : ℂ) - uD r / (r : ℂ)^2) r := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  convert hv.div (complex_radius_hasDerivAt r) hrc using 1
  field_simp
  ring

theorem electricB_hasDerivAt (u uD : ℝ → ℂ) (w : ℂ) (r : ℝ) (hr : r ≠ 0)
    (hu : HasDerivAt u (uD r) r) (hv : HasDerivAt uD w r) :
    HasDerivAt (electricB u uD)
      (5 * uD r / (r : ℂ)^4 - 8 * u r / (r : ℂ)^5 - w / (r : ℂ)^3) r := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hc := complex_radius_hasDerivAt r
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ)^2) (2 * (r : ℂ)) r := by
    convert hc.mul hc using 1 <;> ring_nf
  have h3 : HasDerivAt (fun t : ℝ => (t : ℂ)^3) (3 * (r : ℂ)^2) r := by
    convert h2.mul hc using 1 <;> ring_nf
  have h4 : HasDerivAt (fun t : ℝ => (t : ℂ)^4) (4 * (r : ℂ)^3) r := by
    convert h2.mul h2 using 1
    all_goals ring_nf
  convert ((hu.const_mul 2).div h4 (pow_ne_zero _ hrc)).sub
    (hv.div h3 (pow_ne_zero _ hrc)) using 1
  field_simp
  ring

theorem magneticC_hasDerivAt (κ k : ℂ) (u uD : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0)
    (hu : HasDerivAt u (uD r) r) :
    HasDerivAt (magneticC κ k u)
      ((I * κ^2 / k) * (uD r / (r : ℂ)^2 - 2 * u r / (r : ℂ)^3)) r := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hc := complex_radius_hasDerivAt r
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ)^2) (2 * (r : ℂ)) r := by
    convert hc.mul hc using 1 <;> ring_nf
  unfold magneticC
  generalize I * κ^2 / k = c
  convert (hu.div h2 (pow_ne_zero _ hrc)).const_mul c using 1
  · funext t
    ring
  · field_simp
    ring

/-- The radial Riccati equation constructs an actual complex-frequency
Maxwell dipole away from the origin. No curl equation is a premise. -/
theorem radial_dipole_maxwell (u uD : ℝ → ℂ) (w κ k ε : ℂ)
    (x : Space) (hx : x ≠ 0) (hk : k ≠ 0) (hκ : κ^2 = k^2 * ε)
    (hu : HasDerivAt u (uD ‖x‖) ‖x‖) (hv : HasDerivAt uD w ‖x‖)
    (ho : w = (2 / (‖x‖ : ℂ)^2 - κ^2) * u ‖x‖) :
    ComplexMaxwellAt k ε (dipoleE u uD) (dipoleH κ k u) x := by
  have hr := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hr
  have ha := electricA_hasDerivAt uD w ‖x‖ hr hv
  have hb := electricB_hasDerivAt u uD w ‖x‖ hr hu hv
  have hc := magneticC_hasDerivAt κ k u uD ‖x‖ hr hu
  have hcoef :
      (w / (‖x‖ : ℂ) - uD ‖x‖ / (‖x‖ : ℂ)^2) / (‖x‖ : ℂ) - electricB u uD ‖x‖ =
        -κ^2 * u ‖x‖ / (‖x‖ : ℂ)^2 := by
    rw [ho]
    unfold electricB
    simp only [div_eq_mul_inv, inv_pow]
    ring
  constructor
  · rw [dipoleE, axisField_curl _ _ _ _ x hx ha hb, hcoef]
    ext j
    fin_cases j <;> simp [dipoleH, swirlField, magneticC]
    all_goals field_simp
    all_goals ring_nf
    all_goals norm_num [I_sq]
  · rw [dipoleH, swirlField_curl _ _ x hx hc]
    have htop : (I * κ^2 / k) *
        (uD ‖x‖ / (‖x‖ : ℂ)^2 - 2 * u ‖x‖ / (‖x‖ : ℂ)^3) / (‖x‖ : ℂ) =
        -I * k * ε * electricB u uD ‖x‖ := by
      rw [hκ]
      unfold electricB
      field_simp [hrc, hk]
      ring
    have hbottom : (‖x‖ : ℂ) * ((I * κ^2 / k) *
        (uD ‖x‖ / (‖x‖ : ℂ)^2 - 2 * u ‖x‖ / (‖x‖ : ℂ)^3)) +
        2 * magneticC κ k u ‖x‖ = I * k * ε * electricA uD ‖x‖ := by
      unfold magneticC electricA
      rw [hκ]
      field_simp [hrc, hk]
      ring
    rw [htop, hbottom]
    ext j
    fin_cases j <;> simp [dipoleE, axisField] <;> ring

def scaledRadial (U : ℂ → ℂ) (κ : ℂ) (r : ℝ) : ℂ := U (κ * r)
def scaledRadialD (UD : ℂ → ℂ) (κ : ℂ) (r : ℝ) : ℂ := κ * UD (κ * r)

theorem scaledRadial_hasDerivAt (U UD : ℂ → ℂ) (κ : ℂ) (r : ℝ)
    (h : HasDerivAt U (UD (κ * r)) (κ * r)) :
    HasDerivAt (scaledRadial U κ) (scaledRadialD UD κ r) r := by
  simpa only [scaledRadial, scaledRadialD, Function.comp_def, smul_eq_mul, mul_one] using
    h.scomp r ((complex_radius_hasDerivAt r).const_mul κ)

theorem scaledRadialD_hasDerivAt (U UD : ℂ → ℂ) (κ : ℂ) (hκ : κ ≠ 0)
    (r : ℝ) (hr : r ≠ 0)
    (h : HasDerivAt UD ((2 / (κ * r)^2 - 1) * U (κ * r)) (κ * r)) :
    HasDerivAt (scaledRadialD UD κ)
      ((2 / (r : ℂ)^2 - κ^2) * scaledRadial U κ r) r := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  convert (h.scomp r ((complex_radius_hasDerivAt r).const_mul κ)).const_mul κ using 1
  simp only [smul_eq_mul, scaledRadial]
  field_simp [hrc, hκ]
  ring

def regularE (κ : ℂ) : Field := dipoleE (scaledRadial (psi 1) κ) (scaledRadialD (psiD 1) κ)
def regularH (κ k : ℂ) : Field := dipoleH κ k (scaledRadial (psi 1) κ)
def outgoingE (κ : ℂ) : Field := dipoleE (scaledRadial (xi 1) κ) (scaledRadialD (xiD 1) κ)
def outgoingH (κ k : ℂ) : Field := dipoleH κ k (scaledRadial (xi 1) κ)

/-- The actual regular Riccati function constructs a source-free complex
Maxwell dipole on punctured Euclidean space. Origin removability is separate. -/
theorem regular_dipole_maxwell (κ k ε : ℂ) (hκ : κ ≠ 0) (hk : k ≠ 0)
    (he : κ^2 = k^2 * ε) (x : Space) (hx : x ≠ 0) :
    ComplexMaxwellAt k ε (regularE κ) (regularH κ k) x := by
  have hr := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hr
  have ha := mul_ne_zero hκ hrc
  have hu := scaledRadial_hasDerivAt (psi 1) (psiD 1) κ ‖x‖ (psi_hasDerivAt 1 _ ha)
  have hsecond : HasDerivAt (psiD 1) ((2 / (κ * ‖x‖)^2 - 1) * psi 1 (κ * ‖x‖))
      (κ * ‖x‖) := by simpa only [Nat.cast_one, one_add_one_eq_two, one_mul] using
        OQ14.ModalMatching.psiD_hasDerivAt 1 (κ * ‖x‖) ha
  have hv := scaledRadialD_hasDerivAt (psi 1) (psiD 1) κ hκ ‖x‖ hr hsecond
  exact radial_dipole_maxwell _ _ _ κ k ε x hx hk he hu hv rfl

/-- The actual outgoing Riccati function constructs a source-free complex
Maxwell dipole away from the origin. It is defined by the outgoing exponential. -/
theorem outgoing_dipole_maxwell (κ k ε : ℂ) (hκ : κ ≠ 0) (hk : k ≠ 0)
    (he : κ^2 = k^2 * ε) (x : Space) (hx : x ≠ 0) :
    ComplexMaxwellAt k ε (outgoingE κ) (outgoingH κ k) x := by
  have hr := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hr
  have ha := mul_ne_zero hκ hrc
  have hu := scaledRadial_hasDerivAt (xi 1) (xiD 1) κ ‖x‖ (xi_hasDerivAt 1 _ ha)
  have hsecond : HasDerivAt (xiD 1) ((2 / (κ * ‖x‖)^2 - 1) * xi 1 (κ * ‖x‖))
      (κ * ‖x‖) := by simpa only [Nat.cast_one, one_add_one_eq_two, one_mul] using
        xiD_hasDerivAt 1 (κ * ‖x‖) ha
  have hv := scaledRadialD_hasDerivAt (xi 1) (xiD 1) κ hκ ‖x‖ hr hsecond
  exact radial_dipole_maxwell _ _ _ κ k ε x hx hk he hu hv rfl

end OQ14.ModalDipole

#print axioms OQ14.ModalDipole.coordinate_partial
#print axioms OQ14.ModalDipole.coordinate_differentiableAt
#print axioms OQ14.ModalDipole.radial_coordinate_partial
#print axioms OQ14.ModalDipole.radial_two_coordinates_partial
#print axioms OQ14.ModalDipole.axisField_curl
#print axioms OQ14.ModalDipole.swirlField_curl
#print axioms OQ14.ModalDipole.electricA_hasDerivAt
#print axioms OQ14.ModalDipole.electricB_hasDerivAt
#print axioms OQ14.ModalDipole.magneticC_hasDerivAt
#print axioms OQ14.ModalDipole.radial_dipole_maxwell
#print axioms OQ14.ModalDipole.scaledRadial_hasDerivAt
#print axioms OQ14.ModalDipole.scaledRadialD_hasDerivAt
#print axioms OQ14.ModalDipole.regular_dipole_maxwell
#print axioms OQ14.ModalDipole.outgoing_dipole_maxwell
