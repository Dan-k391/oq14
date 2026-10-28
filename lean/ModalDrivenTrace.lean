import ModalDriven

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.ModalDrivenTrace
open Complex OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalMatching
  OQ14.ModalInterface OQ14.ModalOrigin OQ14.ModalDipole OQ14.ModalDriven

theorem traces (n k : ℂ) (hn : n ≠ 0) (hk : k ≠ 0)
    (x : Space) (hx : ‖x‖ = 1) :
    tangent x (((numerator n k).1/n) • centerE (n*k) x) =
      tangent x (determinant n k • centerE k x + (numerator n k).2 • outgoingE k x) ∧
    tangent x (((numerator n k).1/n) • centerH (n*k) k x) =
      tangent x (determinant n k • centerH k k x + (numerator n k).2 • outgoingH k k x) := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hE := congrArg Prod.snd (numerator_matching n k)
  have hH := congrArg Prod.fst (numerator_matching n k)
  change psiD 1 (n*k) * (numerator n k).1 - xiD 1 k * (numerator n k).2 =
    determinant n k * psiD 1 k at hE
  change n * psi 1 (n*k) * (numerator n k).1 - xi 1 k * (numerator n k).2 =
    determinant n k * psi 1 k at hH
  have he : electricTraceCoefficient n k (numerator n k).1 1 =
      electricTraceCoefficient 1 k (determinant n k) 1 +
      outgoingElectricCoefficient k (numerator n k).2 1 := by
    simp only [electricTraceCoefficient, outgoingElectricCoefficient, ofReal_one, mul_one, div_one, one_mul]
    linear_combination k * hE
  have hh : magneticTraceCoefficient n k (numerator n k).1 1 =
      magneticTraceCoefficient 1 k (determinant n k) 1 +
      outgoingMagneticCoefficient k (numerator n k).2 1 := by
    simp only [magneticTraceCoefficient, outgoingMagneticCoefficient, ofReal_one, mul_one, one_pow, div_one, one_mul]
    linear_combination (I*k) * hH
  have he0 : ((numerator n k).1/n) • centerE (n*k) x = innerE n k (numerator n k).1 x := by
    simp [innerE, centerE_eq_regular _ (mul_ne_zero hn hk) x hx0]
  have hh0 : ((numerator n k).1/n) • centerH (n*k) k x = innerH n k (numerator n k).1 x := by
    simp [innerH, centerH_eq_regular _ k (mul_ne_zero hn hk) x hx0]
  have he1 : determinant n k • centerE k x = innerE 1 k (determinant n k) x := by
    simp [innerE, centerE_eq_regular _ hk x hx0]
  have hh1 : determinant n k • centerH k k x = innerH 1 k (determinant n k) x := by
    simp [innerH, centerH_eq_regular _ k hk x hx0]
  rw [he0, hh0, he1, hh1]
  change tangent x (innerE n k (numerator n k).1 x) =
      tangent x (innerE 1 k (determinant n k) x + outerE k (numerator n k).2 x) ∧
    tangent x (innerH n k (numerator n k).1 x) =
      tangent x (innerH 1 k (determinant n k) x + outerH k (numerator n k).2 x)
  simp only [tangent, map_add]
  constructor
  · rw [← tangent, ← tangent, ← tangent, innerE_trace n k _ hn, innerE_trace 1 k _ one_ne_zero,
      outerE_trace, hx, he]
    ext j; fin_cases j <;> simp <;> ring
  · rw [← tangent, ← tangent, ← tangent, innerH_trace n k _ hn hk,
      innerH_trace 1 k _ one_ne_zero hk, outerH_trace k _ hk, hx, hh]
    ext j; fin_cases j <;> simp <;> ring

end OQ14.ModalDrivenTrace
#print axioms OQ14.ModalDrivenTrace.traces

