import ModalShell
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Actual holomorphic outgoing shell fields

The outgoing Riccati--Hankel function is represented in the Banach algebra
of continuous scalar functions on the compact shell. Its algebra exponential
is evaluated explicitly, so analyticity in the uniform norm is proved before
passing to the actual volume L2 field. No pointwise-to-Banach implication is
assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalShellAnalytic

open Complex OQ14.Maxwell OQ14.GreenKernel OQ14.ModalAlgebra OQ14.ModalDipole
  OQ14.ModalInterface OQ14.ModalShell
open scoped Topology

abbrev ScalarContinuous := C(Shell, ℂ)

def radius : ScalarContinuous :=
  ⟨fun x => (‖(x : Space)‖ : ℂ),
    continuous_ofReal.comp (continuous_subtype_val.norm)⟩

def inverseRadius : ScalarContinuous :=
  ⟨fun x => (radius x)⁻¹, radius.continuous.inv₀ shell_radius_ne_zero⟩

def position (j : Fin 3) : ScalarContinuous :=
  ⟨fun x => ((x : Space) j : ℂ), (coordinate j).continuous.comp continuous_subtype_val⟩

def exponential (k : ℂ) : ScalarContinuous :=
  NormedSpace.exp ℂ ((I*k) • radius)

theorem exponential_apply (k : ℂ) (x : Shell) :
    exponential k x = Complex.exp (I*k*(‖(x : Space)‖ : ℂ)) := by
  have h := NormedSpace.map_exp ℂ (ContinuousMap.evalAlgHom ℂ ℂ x)
    (ContinuousMap.evalCLM (R := ℂ) x).continuous ((I*k) • radius)
  simpa only [exponential, ContinuousMap.evalAlgHom_apply, ContinuousMap.smul_apply,
    radius, ContinuousMap.coe_mk, smul_eq_mul, ← Complex.exp_eq_exp_ℂ] using h

theorem exponential_analytic (k : ℂ) : AnalyticAt ℂ exponential k := by
  exact (NormedSpace.exp_analytic _).comp
    ((analyticAt_const.mul analyticAt_id).smul analyticAt_const)

def polynomial (k : ℂ) : ScalarContinuous :=
  1 + (I/k) • inverseRadius

def polynomialD (k : ℂ) : ScalarContinuous :=
  (-I/k^2) • inverseRadius^2

def hankel (k : ℂ) : ScalarContinuous :=
  -exponential k * polynomial k

def hankelD (k : ℂ) : ScalarContinuous :=
  -exponential k * (I • polynomial k + polynomialD k)

theorem hankel_apply (k : ℂ) (x : Shell) :
    hankel k x = xi 1 (k*(‖(x : Space)‖ : ℂ)) := by
  simp only [hankel, ContinuousMap.mul_apply, ContinuousMap.neg_apply, exponential_apply,
    polynomial, ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.smul_apply,
    inverseRadius, radius, ContinuousMap.coe_mk, smul_eq_mul, xi, p_one]
  norm_num
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem hankelD_apply (k : ℂ) (x : Shell) :
    hankelD k x = xiD 1 (k*(‖(x : Space)‖ : ℂ)) := by
  simp only [hankelD, ContinuousMap.mul_apply, ContinuousMap.neg_apply, exponential_apply,
    polynomial, polynomialD, ContinuousMap.add_apply, ContinuousMap.one_apply,
    ContinuousMap.smul_apply, ContinuousMap.pow_apply, inverseRadius, radius,
    ContinuousMap.coe_mk, smul_eq_mul, xiD, p_one, pD_one]
  norm_num
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, mul_pow]
  ring

theorem hankel_analytic (k : ℂ) (hk : k ≠ 0) : AnalyticAt ℂ hankel k := by
  exact (exponential_analytic k).neg.mul
    (analyticAt_const.add ((analyticAt_const.div analyticAt_id hk).smul analyticAt_const))

theorem hankelD_analytic (k : ℂ) (hk : k ≠ 0) : AnalyticAt ℂ hankelD k := by
  have hp : AnalyticAt ℂ polynomial k :=
    analyticAt_const.add ((analyticAt_const.div analyticAt_id hk).smul analyticAt_const)
  have hd : AnalyticAt ℂ polynomialD k :=
    (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero _ hk)).smul analyticAt_const
  exact (exponential_analytic k).neg.mul ((hp.fun_const_smul (c := I)).add hd)

def radialA (k : ℂ) : ScalarContinuous := k • (hankelD k * inverseRadius)
def radialB (k : ℂ) : ScalarContinuous :=
  (2 : ℂ) • (hankel k * inverseRadius^4) -
    k • (hankelD k * inverseRadius^3)
def radialC (k : ℂ) : ScalarContinuous := (I*k^2/k) • (hankel k * inverseRadius^2)

theorem radialA_analytic (k : ℂ) (hk : k ≠ 0) : AnalyticAt ℂ radialA k :=
  analyticAt_id.smul ((hankelD_analytic k hk).mul analyticAt_const)

theorem radialB_analytic (k : ℂ) (hk : k ≠ 0) : AnalyticAt ℂ radialB k :=
  (((hankel_analytic k hk).mul analyticAt_const).fun_const_smul (c := (2 : ℂ))).sub
    (analyticAt_id.smul ((hankelD_analytic k hk).mul analyticAt_const))

theorem radialC_analytic (k : ℂ) (hk : k ≠ 0) : AnalyticAt ℂ radialC k :=
  ((analyticAt_const.mul (analyticAt_id.pow 2)).div analyticAt_id hk).smul
    ((hankel_analytic k hk).mul analyticAt_const)

def embed (v : PairVector) : ScalarContinuous →L[ℂ] C(Shell, PairVector) :=
  ((ContinuousLinearMap.id ℂ ℂ).smulRight v).compLeftContinuousCompact Shell

def electricBasis (j : Fin 3) : PairVector := (Pi.single j 1, 0)
def magneticBasis (j : Fin 3) : PairVector := (0, Pi.single j 1)

def fieldContinuous (k : ℂ) : C(Shell, PairVector) :=
  embed (electricBasis 0) (radialB k * position 2 * position 0) +
  embed (electricBasis 1) (radialB k * position 2 * position 1) +
  embed (electricBasis 2) (radialA k + radialB k * position 2 * position 2) +
  embed (magneticBasis 0) (radialC k * position 1) +
  embed (magneticBasis 1) (-radialC k * position 0)

theorem fieldContinuous_analytic (k : ℂ) (hk : k ≠ 0) :
    AnalyticAt ℂ fieldContinuous k := by
  have hB (i j : Fin 3) : AnalyticAt ℂ (fun z => radialB z * position i * position j) k :=
    ((radialB_analytic k hk).mul analyticAt_const).mul analyticAt_const
  exact (((((embed (electricBasis 0)).analyticAt _).comp (hB 2 0)).add
    (((embed (electricBasis 1)).analyticAt _).comp (hB 2 1))).add
    (((embed (electricBasis 2)).analyticAt _).comp ((radialA_analytic k hk).add (hB 2 2)))).add
    (((embed (magneticBasis 0)).analyticAt _).comp
      ((radialC_analytic k hk).mul analyticAt_const)) |>.add
    (((embed (magneticBasis 1)).analyticAt _).comp
      ((radialC_analytic k hk).neg.mul analyticAt_const))

theorem embed_apply (v : PairVector) (f : ScalarContinuous) (x : Shell) :
    embed v f x = f x • v := rfl

theorem fieldContinuous_actual (k : ℂ) (x : Shell) :
    fieldContinuous k x = (outerE k 1 x.1, outerH k 1 x.1) := by
  have hA : radialA k x =
      k * xiD 1 (k*‖(x : Space)‖) / (‖(x : Space)‖ : ℂ) := by
    simp only [radialA, ContinuousMap.smul_apply, ContinuousMap.mul_apply, hankelD_apply,
      inverseRadius, radius, ContinuousMap.coe_mk, smul_eq_mul, div_eq_mul_inv]
    ring
  have hB : radialB k x =
      2 * xi 1 (k*‖(x : Space)‖) / (‖(x : Space)‖ : ℂ)^4 -
      k * xiD 1 (k*‖(x : Space)‖) / (‖(x : Space)‖ : ℂ)^3 := by
    simp only [radialB, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.sub_apply, ContinuousMap.pow_apply, hankel_apply, hankelD_apply,
      inverseRadius, radius, ContinuousMap.coe_mk, smul_eq_mul, div_eq_mul_inv, inv_pow]
    ring
  have hC : radialC k x =
      (I*k^2/k) * xi 1 (k*‖(x : Space)‖) / (‖(x : Space)‖ : ℂ)^2 := by
    simp only [radialC, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
      ContinuousMap.pow_apply, hankel_apply, inverseRadius, radius,
      ContinuousMap.coe_mk, smul_eq_mul, div_eq_mul_inv, inv_pow]
    ring
  apply Prod.ext <;> ext j <;> fin_cases j <;>
    simp [fieldContinuous, embed_apply, electricBasis, magneticBasis, position,
      hA, hB, hC, outerE, outerH, outgoingE, outgoingH, dipoleE, dipoleH,
      axisField, swirlField, electricA, electricB, magneticC, scaledRadial, scaledRadialD]

theorem fieldContinuous_eq_unit (k : Frequency) :
    fieldContinuous k.1 = unitContinuous k := by
  apply ContinuousMap.ext
  intro x
  exact fieldContinuous_actual k.1 x

def fieldL2 (k : ℂ) : ShellL2 :=
  ContinuousMap.toLp 2 shellMeasure ℂ (fieldContinuous k)

theorem fieldL2_analytic (k : ℂ) (hk : k ≠ 0) : AnalyticAt ℂ fieldL2 k := by
  let T : C(Shell, PairVector) →L[ℂ] ShellL2 := ContinuousMap.toLp 2 shellMeasure ℂ
  change AnalyticAt ℂ (fun z => T (fieldContinuous z)) k
  exact (T.analyticAt _).comp (fieldContinuous_analytic k hk)

theorem fieldL2_eq_unit (k : Frequency) : fieldL2 k.1 = unitL2 k := by
  unfold fieldL2 unitL2
  rw [fieldContinuous_eq_unit]

theorem fieldL2_actual (k : ℂ) :
    (fieldL2 k : Shell → PairVector) =ᵐ[shellMeasure] fun x =>
      (outerE k 1 x.1, outerH k 1 x.1) := by
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2)
    shellMeasure (fieldContinuous k)] with x hx
  exact hx.trans (fieldContinuous_actual k x)

theorem fieldL2_ne_zero (k : ℂ) (hk : k ≠ 0) : fieldL2 k ≠ 0 := by
  rw [show fieldL2 k = unitL2 ⟨k,hk⟩ from fieldL2_eq_unit ⟨k,hk⟩]
  exact unitL2_ne_zero ⟨k,hk⟩

end OQ14.ModalShellAnalytic


#print axioms OQ14.ModalShellAnalytic.exponential_apply
#print axioms OQ14.ModalShellAnalytic.exponential_analytic
#print axioms OQ14.ModalShellAnalytic.hankel_apply
#print axioms OQ14.ModalShellAnalytic.hankelD_apply
#print axioms OQ14.ModalShellAnalytic.hankel_analytic
#print axioms OQ14.ModalShellAnalytic.hankelD_analytic
#print axioms OQ14.ModalShellAnalytic.radialA_analytic
#print axioms OQ14.ModalShellAnalytic.radialB_analytic
#print axioms OQ14.ModalShellAnalytic.radialC_analytic
#print axioms OQ14.ModalShellAnalytic.fieldContinuous_analytic
#print axioms OQ14.ModalShellAnalytic.embed_apply
#print axioms OQ14.ModalShellAnalytic.fieldContinuous_actual
#print axioms OQ14.ModalShellAnalytic.fieldContinuous_eq_unit
#print axioms OQ14.ModalShellAnalytic.fieldL2_analytic
#print axioms OQ14.ModalShellAnalytic.fieldL2_eq_unit
#print axioms OQ14.ModalShellAnalytic.fieldL2_actual
#print axioms OQ14.ModalShellAnalytic.fieldL2_ne_zero
