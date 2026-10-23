import PhysicalGramBalance

/-! Actual common finite-band TE interpolants with a scalar physical incoming Gram matrix. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PhysicalGramInterpolation
open Complex Maxwell RestrictedTEInputJets RestrictedTEJetMap SymmetricHarmonicJets
open scoped ComplexInnerProductSpace
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem interpolate (r : ℝ) (hr : r≠0) (y : ι → ℝ) (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (n : ℕ) (target : Fin n → Jet ι) :
    ∃ scale : ℝ, 0<scale ∧ ∃ L : ℕ, ∃ A : Fin n → (Index →₀ ℂ),
      (∀ j q, q∈(A j).support → q.val.1≤L) ∧
      (∀ j, fieldJet p (A j)=target j) ∧
      (∀ i j, (⟪RestrictedTEInput.input (A i),RestrictedTEInput.input (A j)⟫ : ℂ)=
        (scale : ℂ)*(if i=j then 1 else 0)) := by
  classical
  have hs := RestrictedTEInputJets.surjective r hr y hy p h0 h1 h2
  choose v hv using (fun j : Fin n => hs (target j))
  obtain ⟨scale,hscale,u,hJ,hG⟩ := PhysicalGramBalance.balance p n v
  have hrep (j : Fin n) : ∃ A : Index →₀ ℂ, RestrictedTEInput.input A=(u j : RestrictedTEInput.Ambient) :=
    (u j).property
  choose A hA using hrep
  have hrange (j : Fin n) : RestrictedTEInput.input.rangeRestrict (A j)=u j := Subtype.ext (hA j)
  let s : Finset Index := Finset.univ.biUnion (fun j : Fin n => (A j).support)
  let L : ℕ := s.sup (fun q => q.val.1)
  refine ⟨scale,hscale,L,A,?_,?_,?_⟩
  · intro j q hq
    exact Finset.le_sup (f := fun q : Index => q.val.1)
      (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,hq⟩)
  · intro j
    rw [← RestrictedTEInputJets.toJet_apply,hrange,hJ,hv]
  · intro i j
    rw [hA i,hA j]
    exact hG i j

end OQ14.PhysicalGramInterpolation
#print axioms OQ14.PhysicalGramInterpolation.interpolate
