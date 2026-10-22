import SphereHarmonicBasis

/-! An actual polynomial bound on the dimensions of the constructed harmonic spaces. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SphereHarmonicDimension

open OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis

abbrev BoundedExponents (l : ℕ) := {d : Fin 3 →₀ ℕ | ∀ i, d i ≤ l}

def boundedExponentEquiv (l : ℕ) : BoundedExponents l ≃ (Fin 3 → Fin (l+1)) where
  toFun d i := ⟨d.val i,Nat.lt_succ_of_le (d.property i)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i : ℕ)),by
    intro i
    simpa using Nat.le_of_lt_succ (f i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    simp
  right_inv f := by
    funext i
    apply Fin.ext
    simp

theorem restrictDegree_finrank (l : ℕ) :
    Module.finrank ℝ (MvPolynomial.restrictDegree (Fin 3) ℝ l)=(l+1)^3 := by
  letI : Fintype (BoundedExponents l) :=
    Fintype.ofEquiv (Fin 3 → Fin (l+1)) (boundedExponentEquiv l).symm
  change Module.finrank ℝ (MvPolynomial.restrictSupport ℝ {d : Fin 3 →₀ ℕ | ∀ i,d i ≤ l})=_
  rw [Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport ℝ _)]
  rw [Fintype.card_congr (boundedExponentEquiv l)]
  simp

theorem harmonicPolynomials_finrank_le (l : ℕ) :
    Module.finrank ℝ (harmonicPolynomials l) ≤ (l+1)^3 := by
  rw [← restrictDegree_finrank]
  apply Submodule.finrank_mono
  exact (harmonicPolynomials_le_totalDegree l).trans
    (MvPolynomial.restrictTotalDegree_le_restrictDegree (Fin 3) ℝ l)

theorem harmonicSpace_finrank_le (l : ℕ) :
    Module.finrank ℝ (harmonicSpace l) ≤ (l+1)^3 :=
  (LinearMap.finrank_range_le (restrictionL2 l)).trans (harmonicPolynomials_finrank_le l)

end OQ14.SphereHarmonicDimension

#print axioms OQ14.SphereHarmonicDimension.boundedExponentEquiv
#print axioms OQ14.SphereHarmonicDimension.restrictDegree_finrank
#print axioms OQ14.SphereHarmonicDimension.harmonicPolynomials_finrank_le
#print axioms OQ14.SphereHarmonicDimension.harmonicSpace_finrank_le
