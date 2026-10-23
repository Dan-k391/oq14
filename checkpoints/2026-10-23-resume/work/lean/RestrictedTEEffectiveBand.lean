import RestrictedTEInputJets
import HarmonicVectorConstants

/-! Remove the zero odd and degree-zero TE columns from actual physical input data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEEffectiveBand
open Complex Maxwell HarmonicPolynomial SymmetricHarmonicJets RestrictedTEIncoming
open RestrictedTEInput RestrictedTEInputJets RestrictedTEJetMap
abbrev Space := FourierL2.Space

def Active (q : Index) : Prop := Even q.val.1 ∧ 2≤q.val.1

theorem column_zero (q : Index) (hq : ¬Active q) : amplitudeColumn q=0 := by
  have hg (i : Fin 3) : MvPolynomial.pderiv i (polynomial q)=0 := by
    by_cases he : Even q.val.1
    · have hl : q.val.1=0 := by
        have hn : ¬2≤q.val.1 := fun h => hq ⟨he,h⟩
        obtain ⟨k,hk⟩ := he
        omega
      apply HarmonicVectorConstants.partial_zero
      simpa only [polynomial,hl] using EvenHarmonicProjection.homogeneous q.val.2 q.val.1 q.property.1
    · have hp : polynomial q=0 := by simp [polynomial,EvenHarmonicProjection.project,he]
      rw [hp]
      exact map_zero _
  have hz : angularMap q=0 := by
    ext n i
    fin_cases i <;> simp [angularMap,DebyeRadialTrace.angularToroidal,complexEvaluate_partial,hg,complexEvaluate,evaluate]
  unfold amplitudeColumn
  rw [hz]
  ext n i
  change (((4*Real.pi : ℂ)*I^q.val.1)*RegularTEIncoming.coefficient q.val.1 true/2)*0=0
  ring

def effective (A : Index →₀ ℂ) : Index →₀ ℂ := by
  classical
  exact A.filter Active

theorem support_active (A : Index →₀ ℂ) (q : Index) (hq : q∈(effective A).support) : Active q := by
  classical
  exact (Finsupp.mem_support_iff.mp hq |> fun h => by
    by_contra hn
    simp [effective,Finsupp.filter_apply,hn] at h)

theorem support_subset (A : Index →₀ ℂ) : (effective A).support⊆A.support := by
  classical
  intro q hq
  exact (Finset.mem_filter.mp (by simpa only [effective,Finsupp.support_filter] using hq)).1

theorem amplitudeMap_eq (A : Index →₀ ℂ) : amplitudeMap (effective A)=amplitudeMap A := by
  classical
  simp only [amplitudeMap,effective,Finsupp.linearCombination_apply,Finsupp.sum,Finsupp.support_filter,
    Finset.sum_filter,Finsupp.filter_apply]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : Active q
  · simp [hq]
  · simp [hq,column_zero q hq]

theorem input_eq (A : Index →₀ ℂ) : input (effective A)=input A := by
  change (1/(Real.sqrt 2 : ℂ)) • ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ (amplitudeMap (effective A))=_
  rw [amplitudeMap_eq]
  rfl

theorem jets_eq {ι : Type*} (p : ι → Space) (A : Index →₀ ℂ) : fieldJet p (effective A)=fieldJet p A := by
  have hzero : input (effective A-A)=0 := by rw [map_sub,input_eq,sub_self]
  have hj := kernel_le p hzero
  change jetMap p (effective A-A)=0 at hj
  rw [map_sub,sub_eq_zero,jetMap_eq,jetMap_eq] at hj
  exact hj

end OQ14.RestrictedTEEffectiveBand
#print axioms OQ14.RestrictedTEEffectiveBand.column_zero
#print axioms OQ14.RestrictedTEEffectiveBand.support_active
#print axioms OQ14.RestrictedTEEffectiveBand.support_subset
#print axioms OQ14.RestrictedTEEffectiveBand.amplitudeMap_eq
#print axioms OQ14.RestrictedTEEffectiveBand.input_eq
#print axioms OQ14.RestrictedTEEffectiveBand.jets_eq
