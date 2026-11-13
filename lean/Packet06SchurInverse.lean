import Packet06SchurAnalytic

/-! Explicit inverse of the rank-one repaired analytic pencil. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SchurInverse
open Packet06RankOneRepair Packet06ScalarSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def polarNumerator (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ) : E →L[ℂ] E :=
  (ψ.comp (Ring.inverse (repair A w ψ))).smulRight (Ring.inverse (repair A w ψ) w)

theorem repaired_left_product (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (hC : IsUnit (repair A w ψ)) (x : E) :
    A (Ring.inverse (repair A w ψ) x) = x-ψ (Ring.inverse (repair A w ψ) x) • w := by
  have h := congrArg (fun L : E →L[ℂ] E => L x) (Ring.mul_inverse_cancel _ hC)
  change A (Ring.inverse (repair A w ψ) x)+ψ (Ring.inverse (repair A w ψ) x) • w = x at h
  exact eq_sub_iff_add_eq.mpr h

theorem inverse_formula (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (hC : IsUnit (repair A w ψ)) (hs : scalar A w ψ ≠ 0) :
    Ring.inverse A = Ring.inverse (repair A w ψ) + (scalar A w ψ)⁻¹ • polarNumerator A w ψ := by
  have hA : IsUnit A := (isUnit_iff_scalar A w ψ hC).mpr hs
  have hAv : A (Ring.inverse (repair A w ψ) w) = scalar A w ψ • w := by
    rw [repaired_left_product A w ψ hC]
    simp only [scalar,sub_smul,one_smul]
  let B := Ring.inverse (repair A w ψ) + (scalar A w ψ)⁻¹ • polarNumerator A w ψ
  have hAB : A*B = 1 := by
    ext x
    change A (Ring.inverse (repair A w ψ) x +
      (scalar A w ψ)⁻¹ • (ψ (Ring.inverse (repair A w ψ) x) • Ring.inverse (repair A w ψ) w)) = x
    rw [map_add,map_smul,map_smul,hAv,repaired_left_product A w ψ hC,smul_smul,smul_smul]
    have hc : (scalar A w ψ)⁻¹ * (ψ (Ring.inverse (repair A w ψ) x) * scalar A w ψ) =
        ψ (Ring.inverse (repair A w ψ) x) := by field_simp
    rw [mul_assoc,hc]
    abel
  calc
    Ring.inverse A = Ring.inverse A*1 := by rw [mul_one]
    _ = Ring.inverse A*(A*B) := by rw [hAB]
    _ = B := by rw [←mul_assoc,Ring.inverse_mul_cancel _ hA,one_mul]

theorem left_annihilates (A : E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (hC : IsUnit (repair A w ψ)) (hs : scalar A w ψ = 0) (x : E) :
    ψ (Ring.inverse (repair A w ψ) (A x)) = 0 := by
  have h := congrArg (fun L : E →L[ℂ] E => L x) (Ring.inverse_mul_cancel _ hC)
  change Ring.inverse (repair A w ψ) (A x + ψ x • w) = x at h
  rw [map_add,map_smul] at h
  have hh := congrArg (fun y : E => ψ y) h
  dsimp only at hh
  rw [map_add,map_smul,(scalar_kernel A w ψ hC hs).2.2.1,smul_eq_mul,mul_one] at hh
  exact add_right_cancel (hh.trans (zero_add (ψ x)).symm)

end OQ14.Packet06SchurInverse
#print axioms OQ14.Packet06SchurInverse.repaired_left_product
#print axioms OQ14.Packet06SchurInverse.inverse_formula
#print axioms OQ14.Packet06SchurInverse.left_annihilates
