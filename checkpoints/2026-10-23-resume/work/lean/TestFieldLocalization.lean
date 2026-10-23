import SourceRegularCorrection

/-! Locality and linearity of the literal Maxwell test pairings. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.TestFieldLocalization
open MeasureTheory Set OQ14.Maxwell OQ14.MaterialMaxwell OQ14.MagneticResponse OQ14.DynamicSource
open OQ14.WeakCurl (next previous)

theorem weak_pair_eq (F : Field) (f : Test) (i : Fin 3) :
    weakCurlPairing F f.val i=curlPair (fieldPair F) i f := by
  fin_cases i <;> simp [weakCurlPairing,curlPair,fieldPair,next,previous,testPartial,GradientProjection.pderivative_apply]

theorem scalar_pair_congr (u v : Space → ℂ) (f : Test)
    (he : ∀ x∈tsupport (f.val : Space → ℂ),u x=v x) :
    (∫ x,u x*f.val x)=∫ x,v x*f.val x := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈tsupport (f.val : Space → ℂ)
  · rw [he x hx]
  · rw [image_eq_zero_of_nmem_tsupport hx,mul_zero,mul_zero]

theorem equation_congr (k : ℝ) (ρ τ : Fin 3 → Space → ℂ) (E H F G : Field) (f : Test)
    (he : ∀ x∈tsupport (f.val : Space → ℂ),E x=F x)
    (hh : ∀ x∈tsupport (f.val : Space → ℂ),H x=G x)
    (hρ : ∀ i x, x∈tsupport (f.val : Space → ℂ) → ρ i x=τ i x)
    (h : ForcedTestLocalization.Equation k ρ E H f) : ForcedTestLocalization.Equation k τ F G f := by
  have hp (A B : Field) (hab : ∀ x∈tsupport (f.val : Space → ℂ),A x=B x) (i : Fin 3) :
      fieldPair A i f=fieldPair B i f := scalar_pair_congr _ _ f (fun x hx => congrFun (hab x hx) i)
  have hc (A B : Field) (hab : ∀ x∈tsupport (f.val : Space → ℂ),A x=B x) (i : Fin 3) :
      curlPair (fieldPair A) i f=curlPair (fieldPair B) i f := by
    rw [←weak_pair_eq,←weak_pair_eq]
    exact congrFun (SourceUnclippedMaxwell.weakCurlPairing_congr_on_support A B f.val hab) i
  intro i
  rw [←hc E F he i,←hc H G hh i,←hp E F he i,←hp H G hh i,
    ←scalar_pair_congr (ρ i) (τ i) f (hρ i)]
  exact h i

theorem fieldPair_smul (c : ℂ) (E : Field) (i : Fin 3) (f : Test) :
    fieldPair (c • E) i f=c*fieldPair E i f := by
  simp only [fieldPair,Pi.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]

theorem curlPair_smul (c : ℂ) (E : Field) (i : Fin 3) (f : Test) :
    curlPair (fieldPair (c • E)) i f=c*curlPair (fieldPair E) i f := by
  unfold curlPair
  rw [fieldPair_smul,fieldPair_smul]
  ring

theorem vacuum_smul (c : ℂ) (k : ℝ) (E H : Field) (h : TestMaxwell k (fun _ => 1) E H) :
    ForcedMaxwellResponse.TestForced k (fun _ _ => 0) (c • E) (c • H) := by
  intro i f
  have he := (h i f).1
  have hh := (h i f).2
  simp only [Complex.ofReal_one,one_mul] at hh
  change curlPair (fieldPair H) i f= -(Complex.I*(k : ℂ))*fieldPair E i f at hh
  constructor
  · rw [curlPair_smul,fieldPair_smul,he]; ring
  · simp only [zero_mul,integral_zero,add_zero]
    rw [curlPair_smul,fieldPair_smul,hh]; ring

end OQ14.TestFieldLocalization
#print axioms OQ14.TestFieldLocalization.weak_pair_eq
#print axioms OQ14.TestFieldLocalization.scalar_pair_congr
#print axioms OQ14.TestFieldLocalization.equation_congr
#print axioms OQ14.TestFieldLocalization.fieldPair_smul
#print axioms OQ14.TestFieldLocalization.curlPair_smul
#print axioms OQ14.TestFieldLocalization.vacuum_smul
