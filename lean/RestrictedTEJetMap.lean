import RestrictedTEIncoming

/-! The literal vector-jet map on finite restricted TE coefficients is linear and onto. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEJetMap
open Complex Maxwell RestrictedTEIncoming SymmetricHarmonicJets
abbrev Space := FourierL2.Space
variable {ι : Type*}
abbrev Jet (ι : Type*) := (ι × Fin 3) → ℂ

def fieldJet (p : ι → Space) (A : Index →₀ ℂ) : Jet ι := fun q =>
  match q.2.val with
  | 0 => DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A) (p q.1) 2
  | 1 => DebyeMaxwell.teMagnetic 1 (RestrictedTEFields.potential 1 A) (p q.1) 0
  | _ => DebyeMaxwell.teMagnetic 1 (RestrictedTEFields.potential 1 A) (p q.1) 1

def column (p : ι → Space) (q : Index) : Jet ι := fun a =>
  ((4*Real.pi : ℂ)*I^q.val.1)*
  match a.2.val with
  | 0 => DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) (p a.1) 2
  | 1 => DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) (p a.1) 0
  | _ => DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) (p a.1) 1

def jetMap (p : ι → Space) : (Index →₀ ℂ) →ₗ[ℂ] Jet ι := Finsupp.linearCombination ℂ (column p)

theorem jetMap_eq (p : ι → Space) (A : Index →₀ ℂ) : jetMap p A=fieldJet p A := by
  funext q
  rcases q with ⟨j,n⟩
  simp only [jetMap,Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  fin_cases n <;> dsimp only [fieldJet,column]
  all_goals try rw [RestrictedTEIncoming.electric_sum]
  all_goals try rw [RestrictedTEIncoming.magnetic_sum]
  all_goals apply Finset.sum_congr rfl
  all_goals intro q _
  all_goals dsimp [coefficient]
  all_goals ring

theorem surjective [Fintype ι] (r : ℝ) (hr : r≠0) (y : ι → ℝ) (hy : Function.Injective y)
    (p : ι → Space) (h0 : ∀ j, p j 0=r) (h1 : ∀ j, p j 1=y j) (h2 : ∀ j, p j 2=0) :
    Function.Surjective (jetMap p) := by
  intro v
  obtain ⟨A,_,_,hJ⟩ := RestrictedTEInterpolation.interpolate 1 (by norm_num) r hr y hy p h0 h1 h2 v
  simp only [ofReal_one] at hJ
  refine ⟨A,?_⟩
  rw [jetMap_eq]
  funext q
  rcases q with ⟨j,n⟩
  obtain ⟨he,hh0,hh1⟩ := hJ j
  fin_cases n
  · exact he
  · exact hh0
  · exact hh1

end OQ14.RestrictedTEJetMap
#print axioms OQ14.RestrictedTEJetMap.jetMap_eq
#print axioms OQ14.RestrictedTEJetMap.surjective
