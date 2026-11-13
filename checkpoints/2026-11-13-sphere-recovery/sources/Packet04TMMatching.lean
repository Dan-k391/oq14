import ModalMatching
import ModalTMIsolation

/-! Exact dielectric factors in the physical TM matching matrix. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet04TMMatching
open Complex OQ14.ModalAlgebra OQ14.ModalMatching

def physicalMatching (l : ℕ) (n z : ℂ) (a b : ℂ) : ℂ × ℂ :=
  (a*psi l (n*z)-b*xi l z, a*(z/n)*psiD l (n*z)-b*z*xiD l z)

theorem determinant_identity (l : ℕ) (n z : ℂ) (hn : n ≠ 0) :
    (psi l (n*z))*(-z*xiD l z)-(-xi l z)*((z/n)*psiD l (n*z)) =
      -(z/n)*tmDet l n z := by
  unfold tmDet
  field_simp [hn]
  ring

theorem physical_matching_eq (l : ℕ) (n z a b : ℂ) (hn : n ≠ 0) :
    physicalMatching l n z a b =
      ((matching l n z (a/n,b)).1, z*(matching l n z (a/n,b)).2) := by
  apply Prod.ext <;> dsimp [physicalMatching, matching] <;> field_simp [hn] <;> ring

theorem matching_zero_of_traces (l : ℕ) (n z a b : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hv : a*psi l (n*z)=b*xi l z)
    (hd : a*(z/n)*psiD l (n*z)=b*z*xiD l z) :
    matching l n z (a/n,b) = 0 := by
  have hm : physicalMatching l n z a b = 0 := by
    apply Prod.ext <;> simp only [physicalMatching, Prod.fst_zero, Prod.snd_zero, hv, hd, sub_self]
  rw [physical_matching_eq l n z a b hn] at hm
  apply Prod.ext
  · simpa only using congrArg (fun v : ℂ × ℂ => v.1) hm
  · have h := congrArg Prod.snd hm
    exact (mul_eq_zero.mp h).resolve_left hz

theorem amplitudes_zero_of_nonzero_determinant (l : ℕ) (n z a b : ℂ)
    (hn : n ≠ 0) (hz : z ≠ 0) (hdet : tmDet l n z ≠ 0)
    (hv : a*psi l (n*z)=b*xi l z)
    (hd : a*(z/n)*psiD l (n*z)=b*z*xiD l z) : a = 0 ∧ b = 0 := by
  have h := solve_left_inverse l n z hdet (a/n,b)
  rw [matching_zero_of_traces l n z a b hn hz hv hd] at h
  have hs : solve l n z 0 = 0 := by simp [solve, adjugate]
  rw [hs] at h
  have ha : a/n = 0 := (congrArg Prod.fst h).symm
  exact ⟨(div_eq_zero_iff.mp ha).resolve_right hn, (congrArg Prod.snd h).symm⟩

theorem non_dipole_amplitudes_zero (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (z : ℂ) (hz : z ≠ 0) (hroot : tmDet 1 n z = 0) (l : ℕ) (hl : l ≠ 1)
    (a b : ℂ) (hv : a*psi l (n*z)=b*xi l z)
    (hd : a*(z/n)*psiD l (n*z)=b*z*xiD l z) : a = 0 ∧ b = 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hn1 : (n : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hn)
  have hnm : (n : ℂ) ≠ -1 := by exact_mod_cast (show n ≠ -1 by linarith)
  exact amplitudes_zero_of_nonzero_determinant l n z a b hn0 hz
    (ModalTMIsolation.distinct_degree_nonzero 1 l n z hl.symm hna hn0 hn1 hnm hz hroot) hv hd

end OQ14.Packet04TMMatching
#print axioms OQ14.Packet04TMMatching.determinant_identity
#print axioms OQ14.Packet04TMMatching.physical_matching_eq
#print axioms OQ14.Packet04TMMatching.matching_zero_of_traces
#print axioms OQ14.Packet04TMMatching.amplitudes_zero_of_nonzero_determinant
#print axioms OQ14.Packet04TMMatching.non_dipole_amplitudes_zero
