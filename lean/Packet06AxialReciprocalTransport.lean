import Packet06AxialComplexTransport
import Packet06PhysicalPairing
import Packet06PhysicalNormalization

/-! Physical bilinear pairing and reciprocal normalization under arbitrary
axial rotation of material and field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06AxialReciprocalTransport
open MeasureTheory Metric Set KernelReciprocity ModalAxialRotation Packet06AxialMaterialTransport
  Packet06AxialComplexTransport Packet06PhysicalNormalization

theorem vectorPair_rotation (θ : ℝ) (u v : VectorFourier.VectorL2) :
    vectorPair (action θ u) (action θ v) = vectorPair u v := by
  rw [Packet06PhysicalPairing.vectorPair_physical, Packet06PhysicalPairing.vectorPair_physical]
  have he : (∫ x : Maxwell.Space, ∑ i : Fin 3,
      action θ u (VectorFourier.coordinateMap x) i * action θ v (VectorFourier.coordinateMap x) i) =
      ∫ x : Maxwell.Space, ∑ i : Fin 3,
        u (VectorFourier.coordinateMap (rotation (-θ) x)) i * v (VectorFourier.coordinateMap (rotation (-θ) x)) i := by
    apply integral_congr_ae
    filter_upwards [action_ae θ u 0,action_ae θ u 1,action_ae θ u 2,
      action_ae θ v 0,action_ae θ v 1,action_ae θ v 2] with x hu0 hu1 hu2 hv0 hv1 hv2
    simp only [Fin.sum_univ_three,hu0,hu1,hu2,hv0,hv1,hv2]
    simp [matrix,Fin.sum_univ_three]
    have h : ((Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2) = 1 := by
      exact_mod_cast Real.cos_sq_add_sin_sq θ
    simp only [Complex.ofReal_cos, Complex.ofReal_sin] at h
    linear_combination (u (VectorFourier.coordinateMap (rotation (-θ) x)) 0 *
      v (VectorFourier.coordinateMap (rotation (-θ) x)) 0 +
      u (VectorFourier.coordinateMap (rotation (-θ) x)) 1 *
      v (VectorFourier.coordinateMap (rotation (-θ) x)) 1) * h
  rw [he]
  have hh := (rotation (-θ)).measurePreserving.integral_comp (rotation (-θ)).toHomeomorph.measurableEmbedding
    (fun x : Maxwell.Space => ∑ i : Fin 3, u (VectorFourier.coordinateMap x) i * v (VectorFourier.coordinateMap x) i)
  simpa [Function.comp_apply] using hh

theorem reciprocalNorm_rotation (θ : ℝ) (c : StaticCoefficient.Coefficient) (z : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (u : VectorFourier.VectorL2) :
    reciprocalNorm (coefficient θ c) R z (action θ u) = reciprocalNorm c R z u := by
  rw [reciprocalNorm_eq_crossing _ _ hR, reciprocalNorm_eq_crossing c R hR,
    derivative_conjugacy θ c R hR hc, vectorPair_rotation]

end OQ14.Packet06AxialReciprocalTransport
#print axioms OQ14.Packet06AxialReciprocalTransport.vectorPair_rotation
#print axioms OQ14.Packet06AxialReciprocalTransport.reciprocalNorm_rotation
