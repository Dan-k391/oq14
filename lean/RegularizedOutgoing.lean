import CompactEntireLift
import RadialRellich

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.RegularizedOutgoing
open Complex OQ14.ModalAlgebra
open scoped Topology

def polynomial (l : ℕ) (z : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (l+1), hankelCoeff l s I * z^(l-s)

def profile (l : ℕ) (z : ℂ) : ℂ := (-I)^(l+1) * exp (I*z) * polynomial l z

theorem polynomial_differentiable (l : ℕ) : Differentiable ℂ (polynomial l) := by
  unfold polynomial
  exact Differentiable.sum fun s _ => (differentiable_id.pow (l-s)).const_mul _

theorem profile_differentiable (l : ℕ) : Differentiable ℂ (profile l) := by
  unfold profile
  exact (((differentiable_const I).mul differentiable_id).cexp.const_mul _).mul (polynomial_differentiable l)

theorem polynomial_eq (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    polynomial l z = z^l * p l z := by
  unfold polynomial p hankelPoly
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hsl : s ≤ l := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have he : z^l * z^(-(s : ℤ)) = z^(l-s) := by
    rw [zpow_neg, zpow_natCast]
    exact (pow_sub₀ z hz hsl).symm
  rw [← he]
  ring

theorem profile_eq (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    profile l z = z^l * xi l z := by
  rw [profile, polynomial_eq l z hz]
  unfold xi
  ring

#print axioms OQ14.RegularizedOutgoing.profile_eq
#print axioms OQ14.RegularizedOutgoing.polynomial_eq
#print axioms OQ14.RegularizedOutgoing.profile_differentiable
#print axioms OQ14.RegularizedOutgoing.polynomial_differentiable
end OQ14.RegularizedOutgoing


