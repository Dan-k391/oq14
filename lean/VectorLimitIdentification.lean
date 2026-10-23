import CentralReactionExpansion
import VectorReactionLimit
import RadialPairedFamily

/-! Reindexing the literal vector limit series and identifying its central-inversion kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VectorLimitIdentification
open Complex OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.SphereHarmonicHilbert
  OQ14.VectorHarmonicNormalization OQ14.VectorReactionTerms OQ14.RadialFiniteLimit
  OQ14.RadialPhaseLimit OQ14.CentralReactionExpansion

def positive (a : PositiveIndex) : TotalIndex := ⟨a.1+1,a.2⟩

theorem positive_injective : Function.Injective positive :=
  (Equiv.sigmaNatSucc Index).symm.injective.comp Sum.inr_injective

theorem positive_hasSum_iff {E : Type*} [AddCommMonoid E] [TopologicalSpace E]
    (f : TotalIndex → E) (hzero : ∀ a : Index 0,f ⟨0,a⟩=0) (s : E) :
    HasSum (fun a => f (positive a)) s ↔ HasSum f s := by
  apply positive_injective.hasSum_iff
  rintro ⟨l,a⟩ hn
  cases l with
  | zero => exact hzero a
  | succ l => exact (hn ⟨⟨l,a⟩,rfl⟩).elim

def limitTerm (tm : Bool) (i j : Fin 3) (gs : List Segment) (a : TotalIndex)
    (p : Space × Space) : ℂ :=
  (-((limitingCoefficients a.1 gs).1/(limitingCoefficients a.1 gs).2+I))*(angularWeight a.1 : ℂ)*
    product tm a i j p

theorem limitTerm_zero (tm : Bool) (i j : Fin 3) (gs : List Segment) (a : Index 0)
    (p : Space × Space) : limitTerm tm i j gs ⟨0,a⟩ p=0 := by
  simp [limitTerm,angularWeight]

theorem weight_positive (a : PositiveIndex) :
    (angularWeight (a.1+1) : ℂ)=DebyeUnitReaction.weight a := by
  simp only [angularWeight,DebyeUnitReaction.weight,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,Nat.cast_add,Nat.cast_one]
  congr 1
  ring

def combinedTerm (q : ℝ) (hq : 0<q) (n : ℕ) (i j : Fin 3) (p : Space × Space)
    (a : TotalIndex) : ℂ :=
  limitTerm true i j (RadialPairedFamily.tm q hq n) a p+
    limitTerm false i j (RadialPairedFamily.te q hq n) a p

def kernel (q : ℝ) (n : ℕ) (i j : Fin 3) (p : Space × Space) : ℂ :=
  I*((((q^(2*n) : ℝ) : ℂ)-1)*evenKernel p.1 p.2 i j+
    ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*oddKernel p.1 p.2 i j)

theorem positive_paired_expansion (q : ℝ) (hq : 0<q) (n : ℕ) (i j : Fin 3) (p : Space × Space) :
    HasSum (fun a => combinedTerm q hq n i j p (positive a)) (kernel q n i j p) := by
  let f : PositiveIndex → ℂ := fun a => sourceFactor q hq n (Sum.inl a)*dyad p.1 p.2 i j (Sum.inl a)
  let g : PositiveIndex → ℂ := fun a => sourceFactor q hq n (Sum.inr a)*dyad p.1 p.2 i j (Sum.inr a)
  have h : HasSum (Sum.elim f g) (kernel q n i j p) := by
    convert pair_reaction_expansion q hq n p.1 p.2 i j using 1
    funext m
    cases m <;> rfl
  have hf : Summable f := by
    simpa only [Function.comp_def,Sum.elim_inl] using h.summable.comp_injective Sum.inl_injective
  have hg : Summable g := by
    simpa only [Function.comp_def,Sum.elim_inr] using h.summable.comp_injective Sum.inr_injective
  have he := (hf.hasSum.sum hg.hasSum).unique h
  rw [← he]
  convert hf.hasSum.add hg.hasSum using 1
  funext a
  dsimp [combinedTerm,limitTerm,positive,RadialPairedFamily.tm,RadialPairedFamily.te,
    product,component,f,g,sourceFactor,dyad,DebyeUnitReaction.electric,DebyeUnitReaction.toroidal]
  rw [weight_positive]
  ring

theorem total_paired_expansion (q : ℝ) (hq : 0<q) (n : ℕ) (i j : Fin 3) (p : Space × Space) :
    HasSum (combinedTerm q hq n i j p) (kernel q n i j p) :=
  (positive_hasSum_iff _ (fun a => by simp only [combinedTerm,limitTerm_zero,add_zero]) _).mp
    (positive_paired_expansion q hq n i j p)

end OQ14.VectorLimitIdentification

#print axioms OQ14.VectorLimitIdentification.positive_injective
#print axioms OQ14.VectorLimitIdentification.positive_hasSum_iff
#print axioms OQ14.VectorLimitIdentification.limitTerm_zero
#print axioms OQ14.VectorLimitIdentification.weight_positive
#print axioms OQ14.VectorLimitIdentification.positive_paired_expansion
#print axioms OQ14.VectorLimitIdentification.total_paired_expansion
