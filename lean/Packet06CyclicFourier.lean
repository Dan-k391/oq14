import Packet06CyclicKernel
import ModalAxialFourier

/-! Cyclic rotation commutes with the actual L² Fourier transform. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicFourier
open MeasureTheory Packet06CyclicRotation Packet06CyclicL2 HalfTurnVectorAction
open scoped FourierTransform SchwartzMap

def schwartzRot : 𝓢(FourierL2.Space, ℂ) →L[ℂ] 𝓢(FourierL2.Space, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rotation.symm.toContinuousLinearEquiv

theorem schwartzRot_apply (f : 𝓢(FourierL2.Space, ℂ)) (x : FourierL2.Space) :
    schwartzRot f x = f (unrotate x) := rfl

theorem pullback_embed (f : 𝓢(FourierL2.Space, ℂ)) :
    pullback (FourierL2.embed f) = FourierL2.embed (schwartzRot f) := by
  apply Lp.ext
  have h := rotation.symm.measurePreserving.quasiMeasurePreserving.ae (FourierL2.embed_ae f)
  filter_upwards [pullback_ae (FourierL2.embed f), h, FourierL2.embed_ae (schwartzRot f)] with x h1 h2 h3
  change FourierL2.embed f (unrotate x) = f (unrotate x) at h2
  rw [h1,h2,h3,schwartzRot_apply]

theorem fourier_schwartzRot (f : 𝓢(FourierL2.Space, ℂ)) :
    SchwartzMap.fourierTransformCLE ℂ (schwartzRot f)=schwartzRot (SchwartzMap.fourierTransformCLE ℂ f) := by
  ext x
  change 𝓕 (fun y => f (unrotate y)) x=𝓕 (fun y => f y) (unrotate x)
  exact Real.fourierIntegral_comp_linearIsometry rotation.symm (fun y => f y) x

theorem fourier_pullback (g : FourierL2.ScalarL2) :
    FourierL2.fourierEquiv (pullback g)=pullback (FourierL2.fourierEquiv g) := by
  have hA : Continuous (fun g : FourierL2.ScalarL2 => FourierL2.fourierEquiv (pullback g)) :=
    FourierL2.fourierEquiv.continuous.comp pullback.continuous
  have hB : Continuous (fun g : FourierL2.ScalarL2 => pullback (FourierL2.fourierEquiv g)) :=
    pullback.continuous.comp FourierL2.fourierEquiv.continuous
  refine FourierL2.embed_denseRange.induction_on g (isClosed_eq hA hB) ?_
  intro f
  rw [pullback_embed, FourierL2.fourierEquiv_embed, FourierL2.fourierEquiv_embed,
    pullback_embed, fourier_schwartzRot]

theorem action_fourier (F : VectorFourier.VectorL2) :
    action (VectorFourier.fourier F)=VectorFourier.fourier (action F) := by
  apply vector_eq_of_component
  intro i
  rw [component_action, HalfTurnParityEquivariance.component_fourier,
    HalfTurnParityEquivariance.component_fourier, component_action]
  exact (fourier_pullback _).symm

end OQ14.Packet06CyclicFourier
#print axioms OQ14.Packet06CyclicFourier.schwartzRot_apply
#print axioms OQ14.Packet06CyclicFourier.pullback_embed
#print axioms OQ14.Packet06CyclicFourier.fourier_schwartzRot
#print axioms OQ14.Packet06CyclicFourier.fourier_pullback
#print axioms OQ14.Packet06CyclicFourier.action_fourier
