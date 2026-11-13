import Packet06TranslationSchwartz

/-! The actual static Newton operator commutes with rigid L² translations. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06TranslationNewton
open MeasureTheory Maxwell Packet06TranslationL2 Packet06TranslationNewtonPairing
open scoped SchwartzMap

theorem newton_action (a : Space) (u : VectorFourier.VectorL2) :
    NewtonL2.newtonOperator (action a u) = action a (NewtonL2.newtonOperator u) := by
  have hA : Continuous (fun v : VectorFourier.VectorL2 => NewtonL2.newtonOperator (action a v)) :=
    NewtonL2.newtonOperator.continuous.comp (action a).continuous
  have hB : Continuous (fun v : VectorFourier.VectorL2 => action a (NewtonL2.newtonOperator v)) :=
    (action a).continuous.comp NewtonL2.newtonOperator.continuous
  refine NewtonL2.schwartzVector_denseRange.induction_on u (isClosed_eq hA hB) ?_
  intro f
  apply HalfTurnVectorAction.vector_eq_of_component
  intro i
  change NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (action a (VectorFourier.schwartzVector f))) i =
    NewtonL2.physicalCoordinate (action a (NewtonL2.newtonOperator (VectorFourier.schwartzVector f))) i
  apply NewtonL2.scalar_pairing_ext
  intro g
  rw [Packet06TranslationSchwartz.action_schwartz, NewtonL2.newtonOperator_spatial_pairing]
  change _ = ∫ x, DynamicConvolution.component i (action a (NewtonL2.newtonOperator (VectorFourier.schwartzVector f))) x * g x
  rw [component_action, StaticBallTranslation.scalar_pairing]
  change _ = ∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (VectorFourier.schwartzVector f)) i x * (NewtonConvolution.translate a g) x
  rw [NewtonL2.newtonOperator_spatial_pairing]
  apply Finset.sum_congr rfl
  intro j hj
  exact weakConvolution_translate a (f j) g i j

end OQ14.Packet06TranslationNewton
#print axioms OQ14.Packet06TranslationNewton.newton_action
