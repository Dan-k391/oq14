import Mathlib.LinearAlgebra.Matrix.PosDef

/-! An actual positive scalar Gram completion from the Hermitian spectral theorem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HermitianGramCompletion
open Complex Matrix
open scoped ComplexOrder

theorem positive_shift {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ) (hG : G.IsHermitian) :
    ∃ scale : ℝ, 0<scale ∧ ((scale : ℂ) • (1 : Matrix n n ℂ)-G).PosSemidef := by
  let scale : ℝ := 1+∑ i : n, |hG.eigenvalues i|
  have hscale : 0<scale := by dsimp [scale]; positivity
  have hb (i : n) : hG.eigenvalues i≤scale := by
    have hs : |hG.eigenvalues i|≤∑ j : n, |hG.eigenvalues j| :=
      Finset.single_le_sum (f := fun j => |hG.eigenvalues j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [scale]
    linarith [le_abs_self (hG.eigenvalues i)]
  let D : Matrix n n ℂ := diagonal (fun i => ((scale-hG.eigenvalues i : ℝ) : ℂ))
  have hD : D.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (fun i => by
    exact_mod_cast (sub_nonneg.mpr (hb i)))
  have he : D=(scale : ℂ) • (1 : Matrix n n ℂ)-diagonal (RCLike.ofReal ∘ hG.eigenvalues) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [D]
    · simp [D,Matrix.one_apply,hij]
  have hp := hD.mul_mul_conjTranspose_same (hG.eigenvectorUnitary : Matrix n n ℂ)
  rw [he,Matrix.mul_sub,Matrix.sub_mul] at hp
  have hscalar : (hG.eigenvectorUnitary : Matrix n n ℂ)*((scale : ℂ) • (1 : Matrix n n ℂ))*
      (hG.eigenvectorUnitary : Matrix n n ℂ)ᴴ=(scale : ℂ) • (1 : Matrix n n ℂ) := by
    have hu : (hG.eigenvectorUnitary : Matrix n n ℂ)*(hG.eigenvectorUnitary : Matrix n n ℂ)ᴴ=1 :=
      unitary.coe_mul_star_self hG.eigenvectorUnitary
    simp [Matrix.mul_smul,Matrix.smul_mul,hu]
  have hspec : G=(hG.eigenvectorUnitary : Matrix n n ℂ)*diagonal (RCLike.ofReal ∘ hG.eigenvalues)*
      (hG.eigenvectorUnitary : Matrix n n ℂ)ᴴ := hG.spectral_theorem
  rw [hscalar,← hspec] at hp
  exact ⟨scale,hscale,hp⟩

theorem completion {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ) (hG : G.IsHermitian) :
    ∃ scale : ℝ, 0<scale ∧ ∃ B : Matrix n n ℂ, Bᴴ*B=(scale : ℂ) • (1 : Matrix n n ℂ)-G := by
  obtain ⟨scale,hscale,hp⟩ := positive_shift G hG
  obtain ⟨B,hB⟩ := Matrix.posSemidef_iff_eq_transpose_mul_self.mp hp
  exact ⟨scale,hscale,B,hB.symm⟩

end OQ14.HermitianGramCompletion
#print axioms OQ14.HermitianGramCompletion.positive_shift
#print axioms OQ14.HermitianGramCompletion.completion
