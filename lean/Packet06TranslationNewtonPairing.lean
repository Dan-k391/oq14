import Packet06TranslationL2

/-! Translation covariance of the distributional Newton-Hessian pairing. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06TranslationNewtonPairing
open MeasureTheory Maxwell
open scoped SchwartzMap

theorem translate_comp (a b : Space) (f : 𝓢(Space, ℂ)) :
    NewtonConvolution.translate a (NewtonConvolution.translate b f) = NewtonConvolution.translate (a+b) f := by
  ext x
  simp only [NewtonConvolution.translate_apply]
  congr 1
  abel

theorem weakConvolution_translate (a : Space) (f g : 𝓢(Space, ℂ)) (i j : Fin 3) :
    NewtonConvolution.weakConvolution (NewtonConvolution.translate (-a) f) i j g =
      NewtonConvolution.weakConvolution f i j (NewtonConvolution.translate a g) := by
  unfold NewtonConvolution.weakConvolution
  have h := integral_add_right_eq_self (μ := (volume : Measure Space))
    (fun y : Space => (NewtonConvolution.translate (-a) f) y *
      NewtonHessian.weakHessian i j (NewtonConvolution.translate y g)) a
  rw [← h]
  apply integral_congr_ae
  filter_upwards with y
  rw [NewtonConvolution.translate_apply]
  have he : y + a + -a = y := by abel
  rw [he,translate_comp]

end OQ14.Packet06TranslationNewtonPairing
#print axioms OQ14.Packet06TranslationNewtonPairing.translate_comp
#print axioms OQ14.Packet06TranslationNewtonPairing.weakConvolution_translate
