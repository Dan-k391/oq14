import PhysicalGramInterpolation

/-! Physical unit-power normalization preserves literal finite TE realizations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PhysicalGramNormalization
open Complex Maxwell RestrictedTEInputJets RestrictedTEJetMap SymmetricHarmonicJets
open scoped ComplexInnerProductSpace ComplexConjugate
abbrev Space := FourierL2.Space

theorem normalize_orthonormal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (n : ℕ) (v : Fin n → V) (scale : ℝ) (hs : 0<scale)
    (hG : ∀ i j, (⟪v i,v j⟫ : ℂ)=(scale : ℂ)*(if i=j then 1 else 0)) :
    Orthonormal ℂ (fun j => (1/(Real.sqrt scale : ℂ)) • v j) := by
  have he : ((Real.sqrt scale : ℝ) : ℂ)^2=(scale : ℂ) := by exact_mod_cast Real.sq_sqrt hs.le
  have hsq : (Real.sqrt scale : ℂ)≠0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
  have hc : conj (1/(Real.sqrt scale : ℂ))*(1/(Real.sqrt scale : ℂ))*(scale : ℂ)=1 := by
    simp
    field_simp
    simpa only [pow_two] using he.symm
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [inner_smul_left,inner_smul_right,hG]
  by_cases hij : i=j
  · simpa only [if_pos hij,mul_one,mul_assoc] using hc
  · simp [hij]

theorem interpolate {ι : Type*} [Fintype ι] (r : ℝ) (hr : r≠0) (y : ι → ℝ)
    (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (n : ℕ) (target : Fin n → Jet ι) :
    ∃ scale : ℝ, 0<scale ∧ ∃ L : ℕ, ∃ A : Fin n → (Index →₀ ℂ),
      (∀ j q, q∈(A j).support → q.val.1≤L) ∧
      (∀ j, fieldJet p (A j)=(1/(Real.sqrt scale : ℂ)) • target j) ∧
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) := by
  classical
  obtain ⟨scale,hs,L,A,hL,hJ,hG⟩ := PhysicalGramInterpolation.interpolate r hr y hy p h0 h1 h2 n target
  let c : ℂ := 1/(Real.sqrt scale : ℂ)
  refine ⟨scale,hs,L,(fun j => c • A j),?_,?_,?_⟩
  · intro j q hq
    apply hL j q
    by_contra hz
    have hzero := Finsupp.not_mem_support_iff.mp hz
    have hnonzero := Finsupp.mem_support_iff.mp hq
    simp only [Finsupp.smul_apply,hzero,smul_zero,ne_eq,not_true_eq_false] at hnonzero
  · intro j
    rw [← jetMap_eq,map_smul,jetMap_eq,hJ]
  · have hn := normalize_orthonormal n (fun j => RestrictedTEInput.input (A j)) scale hs hG
    simpa only [map_smul] using hn

end OQ14.PhysicalGramNormalization
#print axioms OQ14.PhysicalGramNormalization.normalize_orthonormal
#print axioms OQ14.PhysicalGramNormalization.interpolate
