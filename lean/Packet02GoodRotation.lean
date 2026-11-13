import Packet02GoodSet
import Packet02SourceSymmetry
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02GoodRotation
open MeasureTheory OQ14.Maxwell OQ14.ModalAxialRotation OQ14.ModalWeightedMode

theorem integrable_rotation (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (θ : ℝ) (x : Space) (K : Space → ℂ)
    (hK : ∀ v, K (rotation θ v) = K v)
    (hI : ∀ b, Integrable (fun y => DynamicVolume.source (coefficient n hn) u b y * K (x-y)))
    (l : Fin 3) : Integrable (fun y => DynamicVolume.source (coefficient n hn) u l y * K (rotation θ x-y)) := by
  apply ((rotation θ).measurePreserving.integrable_comp_emb (rotation θ).toHomeomorph.measurableEmbedding).mp
  apply (integrable_finset_sum _ (fun b _ => (hI b).const_mul (matrix θ l b))).congr
  filter_upwards [Packet02SourceSymmetry.source_covariant n hn u hu θ l] with y hy
  change (∑ b : Fin 3, matrix θ l b * (DynamicVolume.source (coefficient n hn) u b y * K (x-y))) = _
  simp only [Function.comp_apply]
  rw [← map_sub (rotation θ), hK, hy, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem integrable_reflection (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ ModalMeridionalReflection.electricSector) (x : Space) (K : Space → ℂ)
    (hK : ∀ v, K (ModalMeridionalReflection.reflection v) = K v)
    (hI : ∀ b, Integrable (fun y => DynamicVolume.source (coefficient n hn) u b y * K (x-y)))
    (l : Fin 3) : Integrable (fun y => DynamicVolume.source (coefficient n hn) u l y * K (ModalMeridionalReflection.reflection x-y)) := by
  let S := ModalMeridionalReflection.reflection
  have hf : ModalMeridionalReflection.action u = u := by
    have h := hu.2
    change (ModalMeridionalReflection.action - 1) u = 0 at h
    simpa using sub_eq_zero.mp h
  have hs := S.measurePreserving.quasiMeasurePreserving.ae (ModalMeridionalStatic.source_action n hn u l)
  apply (S.measurePreserving.integrable_comp_emb S.toHomeomorph.measurableEmbedding).mp
  apply ((hI l).const_mul (ModalMeridionalReflection.sign l : ℂ)).congr
  filter_upwards [hs] with y hy
  simp only [Function.comp_apply]
  change DynamicVolume.source (coefficient n hn) (ModalMeridionalReflection.action u) l (S y) = _ at hy
  rw [hf, ModalMeridionalReflection.reflection_reflection] at hy
  rw [← map_sub S, hK, hy]
  ring

theorem good_rotation (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (θ : ℝ) (x : Space) :
    Packet02GoodSet.good n hn u (rotation θ x) ↔ Packet02GoodSet.good n hn u x := by
  have forward (α : ℝ) (y : Space) : Packet02GoodSet.good n hn u y →
      Packet02GoodSet.good n hn u (rotation α y) := by
    intro hy l
    apply integrable_rotation n hn u hu α y Packet02GoodSet.inverseSquare _ hy l
    intro v
    simp [Packet02GoodSet.inverseSquare, show ‖rotation α v‖ = ‖v‖ from (rotation α).norm_map v]
  constructor
  · intro h
    have hh := forward (-θ) (rotation θ x) h
    change Packet02GoodSet.good n hn u (spatial (-θ) (spatial θ x)) at hh
    simpa only [spatial_inverse] using hh
  · exact forward θ x

theorem good_reflection (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ ModalMeridionalReflection.electricSector) (x : Space) :
    Packet02GoodSet.good n hn u (ModalMeridionalReflection.reflection x) ↔ Packet02GoodSet.good n hn u x := by
  have forward (y : Space) : Packet02GoodSet.good n hn u y →
      Packet02GoodSet.good n hn u (ModalMeridionalReflection.reflection y) := by
    intro hy l
    apply integrable_reflection n hn u hu y Packet02GoodSet.inverseSquare _ hy l
    intro v
    simp [Packet02GoodSet.inverseSquare, ModalMeridionalReflection.reflection.norm_map]
  constructor
  · intro h
    simpa only [ModalMeridionalReflection.reflection_reflection] using forward _ h
  · exact forward x

#print axioms OQ14.Packet02GoodRotation.integrable_rotation
#print axioms OQ14.Packet02GoodRotation.integrable_reflection
#print axioms OQ14.Packet02GoodRotation.good_rotation
#print axioms OQ14.Packet02GoodRotation.good_reflection
end OQ14.Packet02GoodRotation
