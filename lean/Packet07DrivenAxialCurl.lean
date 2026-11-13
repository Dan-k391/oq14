import Packet07DrivenAxialDerivativePair

/-! Distributional curl transforms under any axial rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenAxialCurl
open MeasureTheory Maxwell DynamicSource MaterialMaxwell MagneticResponse ModalAxialRotation
  Packet07DrivenAxialTests Packet07DrivenAxialPair Packet07DrivenAxialDerivativePair
open WeakCurl (next previous)

theorem curl_pair_zero (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (f : Test) :
    curlPair (fieldPair (rotateField θ F)) 0 f =
      (Real.cos θ : ℂ)*curlPair (fieldPair F) 0 (rotateTest θ f) -
      (Real.sin θ : ℂ)*curlPair (fieldPair F) 1 (rotateTest θ f) := by
  simp only [curlPair,next,previous,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rw [field_pair_one θ F hF,field_pair_two]
  have h0 := pair_partial_zero θ F hF 2 f
  have h1 := pair_partial_one θ F hF 2 f
  have h2a := pair_partial_two θ F 0 f
  have h2b := pair_partial_two θ F 1 f
  have htrig : ((Real.cos θ : ℂ)^2+(Real.sin θ : ℂ)^2)=1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [h2a,h2b]
  linear_combination (Real.cos θ : ℂ)*h1 + (Real.sin θ : ℂ)*h0 +
    (fieldPair F 2 (rotateTest θ (testPartial 1 f)))*htrig

theorem curl_pair_one (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (f : Test) :
    curlPair (fieldPair (rotateField θ F)) 1 f =
      (Real.sin θ : ℂ)*curlPair (fieldPair F) 0 (rotateTest θ f) +
      (Real.cos θ : ℂ)*curlPair (fieldPair F) 1 (rotateTest θ f) := by
  simp only [curlPair,next,previous,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  rw [field_pair_zero θ F hF,field_pair_two]
  have h0 := pair_partial_zero θ F hF 2 f
  have h1 := pair_partial_one θ F hF 2 f
  have h2a := pair_partial_two θ F 0 f
  have h2b := pair_partial_two θ F 1 f
  have htrig : ((Real.cos θ : ℂ)^2+(Real.sin θ : ℂ)^2)=1 := by exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [h2a,h2b]
  linear_combination (Real.sin θ : ℂ)*h1 - (Real.cos θ : ℂ)*h0 -
    (fieldPair F 2 (rotateTest θ (testPartial 0 f)))*htrig

theorem curl_pair_two (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (f : Test) :
    curlPair (fieldPair (rotateField θ F)) 2 f = curlPair (fieldPair F) 2 (rotateTest θ f) := by
  simp only [curlPair,next,previous,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  change fieldPair (rotateField θ F) 0 (testPartial 1 f) - fieldPair (rotateField θ F) 1 (testPartial 0 f) =
    fieldPair F 0 (testPartial 1 (rotateTest θ f)) - fieldPair F 1 (testPartial 0 (rotateTest θ f))
  rw [field_pair_zero θ F hF,field_pair_one θ F hF]
  rw [pair_partial_one θ F hF 0 f,pair_partial_zero θ F hF 1 f]
  ring
end OQ14.Packet07DrivenAxialCurl
#print axioms OQ14.Packet07DrivenAxialCurl.curl_pair_zero
#print axioms OQ14.Packet07DrivenAxialCurl.curl_pair_one
#print axioms OQ14.Packet07DrivenAxialCurl.curl_pair_two
