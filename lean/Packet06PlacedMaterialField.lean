import Packet06PlacedAction
import Packet06GreenSource
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PlacedMaterialField
open MeasureTheory Metric OQ14.Maxwell OQ14.Packet06CyclicRotation OQ14.Packet06PlacedKernel
open OQ14.WeakCurl (previous)

theorem coefficient_value (s : ℝ) (a x : Maxwell.Space) (c : StaticCoefficient.Coefficient) :
    (placedCoefficient s a c).value (VectorFourier.coordinateMap x) =
      c.value (VectorFourier.coordinateMap (unrotate (s • (x-a)))) := by
  rw [placedCoefficient,Packet06TranslationMaterial.coefficient_value,
    FrequencyScalingMaxwell.scaleCoeff_value,← FrequencyScalingMaxwell.coordinateMap_smul,
    Packet06CyclicMaterial.coefficient_value]

theorem kernel_weighted_response_ae (c : StaticCoefficient.Coefficient) (z : ℂ) (S T : ℝ)
    (hST : S ≤ T) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x)=0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u=0) (i : Fin 3) :
    ∀ᵐ x : Maxwell.Space, u (VectorFourier.coordinateMap x) i =
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
        Packet06LocalPencil.response c z S T u (VectorFourier.coordinateMap x) i := by
  have h := Packet06GreenSource.solved_weighted_response c z S T hST u 0 hc hu
  simp only [sub_zero] at h
  have hm := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c (Packet06LocalPencil.response c z S T u))
  filter_upwards [hm] with x hx
  have hi := congrArg (fun v : VectorFourier.Vector => v i) hx
  simp only [PiLp.smul_apply,smul_eq_mul,h] at hi
  exact hi

theorem placed_response_material_ae (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (U : ℝ) (hU : R/s+‖a‖ ≤ U) (i : Fin 3) :
    ∀ᵐ y : Maxwell.Space, c.value (VectorFourier.coordinateMap (unrotate (s • (y-a)))) ≠ 0 →
      Packet06LocalPencil.response (placedCoefficient s a c) ((s : ℂ)*z) (R/s+‖a‖) U
        (placedUnknown s a u) (VectorFourier.coordinateMap y) i =
      ((Real.sqrt s*s : ℝ) : ℂ)*Packet06LocalPencil.response c z R T u
        (VectorFourier.coordinateMap (unrotate (s • (y-a)))) (previous i) := by
  obtain ⟨hpc,hpk,_,_⟩ := Packet06PlacedKernel.placed_normalized_kernel c R hR hc z u hu hN s hs a
  have hp := kernel_weighted_response_ae (placedCoefficient s a c) ((s : ℂ)*z) (R/s+‖a‖) U hU
    (placedUnknown s a u) hpc hpk i
  have ho := kernel_weighted_response_ae c z R T hRT u hc hu (previous i)
  have hor := rotation.symm.measurePreserving.quasiMeasurePreserving.ae ho
  have hos := DilationL2.ae_smul_space s hs.ne' hor
  have hot := (measurePreserving_add_right (volume : Measure Maxwell.Space) (-a)).quasiMeasurePreserving.ae hos
  filter_upwards [hp,Packet06PlacedAction.placed_unknown_ae s hs a u i,hot] with y hp hu' ho'
  intro hχ
  have hsqrt : (Real.sqrt (c.value (VectorFourier.coordinateMap (unrotate (s • (y-a))))) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact Real.sqrt_ne_zero'.mpr ((c.nonnegative _).lt_of_ne' hχ)
  rw [coefficient_value] at hp
  apply mul_left_cancel₀ hsqrt
  rw [←hp,hu']
  change u (VectorFourier.coordinateMap (unrotate (s • (y-a)))) (previous i) =
    (Real.sqrt (c.value (VectorFourier.coordinateMap (unrotate (s • (y-a))))) : ℂ)*
      Packet06LocalPencil.response c z R T u (VectorFourier.coordinateMap (unrotate (s • (y-a)))) (previous i) at ho'
  rw [ho']
  ring
#print axioms OQ14.Packet06PlacedMaterialField.coefficient_value
#print axioms OQ14.Packet06PlacedMaterialField.kernel_weighted_response_ae
#print axioms OQ14.Packet06PlacedMaterialField.placed_response_material_ae
end OQ14.Packet06PlacedMaterialField
