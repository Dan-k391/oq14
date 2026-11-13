import ModalAxialRotation
import ModalMeridionalStatic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02SourceSymmetry
open MeasureTheory OQ14.Maxwell OQ14.ModalAxialRotation OQ14.ModalWeightedMode

theorem source_action (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) (θ : ℝ) (i : Fin 3) :
    (fun x => DynamicVolume.source (coefficient n hn) (action θ u) i x) =ᵐ[volume]
      fun x => ∑ j : Fin 3, matrix θ i j * DynamicVolume.source (coefficient n hn) u j (rotation (-θ) x) := by
  filter_upwards [action_ae θ u i] with x hx
  unfold DynamicVolume.source
  rw [hx]
  change _ = ∑ j : Fin 3, matrix θ i j * ((Real.sqrt ((coefficient n hn).value (VectorFourier.coordinateMap (spatial (-θ) x))) : ℂ) * u (VectorFourier.coordinateMap (rotation (-θ) x)) j)
  rw [material_invariant n hn (-θ) x]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem source_covariant (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (θ : ℝ) (i : Fin 3) :
    (fun x => DynamicVolume.source (coefficient n hn) u i (rotation θ x)) =ᵐ[volume]
      fun x => ∑ j : Fin 3, matrix θ i j * DynamicVolume.source (coefficient n hn) u j x := by
  have hf : action θ u = u := by
    simp only [axialSector, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at hu
    exact hu θ
  have h := (rotation θ).measurePreserving.quasiMeasurePreserving.ae (source_action n hn u θ i)
  filter_upwards [h] with x hx
  change DynamicVolume.source (coefficient n hn) (action θ u) i (rotation θ x) =
    ∑ j : Fin 3, matrix θ i j * DynamicVolume.source (coefficient n hn) u j (spatial (-θ) (spatial θ x)) at hx
  rw [hf, spatial_inverse] at hx
  exact hx

#print axioms OQ14.Packet02SourceSymmetry.source_action
#print axioms OQ14.Packet02SourceSymmetry.source_covariant
end OQ14.Packet02SourceSymmetry
