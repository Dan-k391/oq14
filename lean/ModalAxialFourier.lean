import ModalAxialRotation
import HalfTurnParityEquivariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ModalAxialFourier
open MeasureTheory OQ14.ModalAxialRotation OQ14.HalfTurnVectorAction OQ14.DynamicConvolution
open scoped FourierTransform SchwartzMap

def schwartzRot (θ : ℝ) : 𝓢(FourierL2.Space, ℂ) →L[ℂ] 𝓢(FourierL2.Space, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (rotation (-θ)).toContinuousLinearEquiv

theorem schwartzRot_apply (θ : ℝ) (f : 𝓢(FourierL2.Space, ℂ)) (x : FourierL2.Space) :
    schwartzRot θ f x = f (rotation (-θ) x) := rfl

theorem pullback_embed (θ : ℝ) (f : 𝓢(FourierL2.Space, ℂ)) :
    pullback θ (FourierL2.embed f) = FourierL2.embed (schwartzRot θ f) := by
  apply Lp.ext
  have h := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae (FourierL2.embed_ae f)
  filter_upwards [pullback_ae θ (FourierL2.embed f), h, FourierL2.embed_ae (schwartzRot θ f)] with x h1 h2 h3
  rw [h1,h2,h3,schwartzRot_apply]

theorem fourier_schwartzRot (θ : ℝ) (f : 𝓢(FourierL2.Space, ℂ)) :
    SchwartzMap.fourierTransformCLE ℂ (schwartzRot θ f)=schwartzRot θ (SchwartzMap.fourierTransformCLE ℂ f) := by
  ext x
  change 𝓕 (fun y => f (rotation (-θ) y)) x=𝓕 (fun y => f y) (rotation (-θ) x)
  exact Real.fourierIntegral_comp_linearIsometry (rotation (-θ)) (fun y => f y) x

theorem fourier_pullback (θ : ℝ) (g : FourierL2.ScalarL2) :
    FourierL2.fourierEquiv (pullback θ g)=pullback θ (FourierL2.fourierEquiv g) := by
  have hA : Continuous (fun g : FourierL2.ScalarL2 => FourierL2.fourierEquiv (pullback θ g)) :=
    FourierL2.fourierEquiv.continuous.comp (pullback θ).continuous
  have hB : Continuous (fun g : FourierL2.ScalarL2 => pullback θ (FourierL2.fourierEquiv g)) :=
    (pullback θ).continuous.comp FourierL2.fourierEquiv.continuous
  refine FourierL2.embed_denseRange.induction_on g (isClosed_eq hA hB) ?_
  intro f
  rw [pullback_embed, FourierL2.fourierEquiv_embed, FourierL2.fourierEquiv_embed,
    pullback_embed, fourier_schwartzRot]

theorem action_fourier (θ : ℝ) (F : VectorFourier.VectorL2) :
    action θ (VectorFourier.fourier F)=VectorFourier.fourier (action θ F) := by
  apply vector_eq_of_component
  intro i
  rw [component_action, HalfTurnParityEquivariance.component_fourier, component_action]
  simp only [map_sum, map_smul, fourier_pullback, HalfTurnParityEquivariance.component_fourier]

#print axioms OQ14.ModalAxialFourier.fourier_pullback
#print axioms OQ14.ModalAxialFourier.action_fourier
end OQ14.ModalAxialFourier
