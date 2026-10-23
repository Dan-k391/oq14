import PhysicalGramNormalization
import RestrictedTEEffectiveBand

/-! Actual common finite even-degree TE band with orthonormal physical incoming inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PhysicalTEBandInterpolation
open Maxwell SymmetricHarmonicJets RestrictedTEJetMap RestrictedTEEffectiveBand
open scoped ComplexInnerProductSpace
abbrev Space := FourierL2.Space

theorem interpolate {ι : Type*} [Fintype ι] (r : ℝ) (hr : r≠0) (y : ι → ℝ)
    (hy : Function.Injective y) (p : ι → Space)
    (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0)
    (n : ℕ) (target : Fin n → Jet ι) :
    ∃ scale : ℝ, 0<scale ∧ ∃ L : ℕ, ∃ A : Fin n → (Index →₀ ℂ),
      (∀ j q, q∈(A j).support → Even q.val.1 ∧ 2≤q.val.1 ∧ q.val.1≤L) ∧
      (∀ j, fieldJet p (A j)=(1/(Real.sqrt scale : ℂ)) • target j) ∧
      Orthonormal ℂ (fun j => RestrictedTEInput.input (A j)) := by
  obtain ⟨scale,hs,L,A,hL,hJ,hO⟩ := PhysicalGramNormalization.interpolate r hr y hy p h0 h1 h2 n target
  refine ⟨scale,hs,L,(fun j => effective (A j)),?_,?_,?_⟩
  · intro j q hq
    exact ⟨(support_active (A j) q hq).1,(support_active (A j) q hq).2,
      hL j q (support_subset (A j) hq)⟩
  · intro j
    rw [jets_eq,hJ]
  · simpa only [input_eq] using hO

end OQ14.PhysicalTEBandInterpolation
#print axioms OQ14.PhysicalTEBandInterpolation.interpolate
