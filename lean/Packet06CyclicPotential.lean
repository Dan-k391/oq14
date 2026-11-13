import Packet06CyclicSource
import Packet06AxialConvolution

/-! The actual material-source dyadic potential rotates exactly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06CyclicPotential
open MeasureTheory Maxwell Packet06CyclicRotation Packet06CyclicL2 Packet06CyclicMaterial
open WeakCurl (previous)

theorem potential_rotate (c : StaticCoefficient.Coefficient) (k : ℝ)
    (u : VectorFourier.VectorL2) (x : Space) (i : Fin 3) :
    Packet06AxialConvolution.potential (coefficient c) k (action u) x i =
      Packet06AxialConvolution.potential c k u (unrotate x) (previous i) := by
  have hone (j : Fin 3) :
      (∫ y : Space, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source (coefficient c) (action u) j y) =
      ∫ y : Space, DyadicKernel.remainder k (unrotate x-y) (previous i) (previous j) *
        DynamicVolume.source c u (previous j) y := by
    have hsource : (∫ y : Space, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source (coefficient c) (action u) j y) =
        ∫ y : Space, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u (previous j) (unrotate y) := by
      apply integral_congr_ae
      filter_upwards [Packet06CyclicSource.source_action c u j] with y hy
      rw [hy]
    rw [hsource]
    have h := rotation.measurePreserving.integral_comp rotation.toHomeomorph.measurableEmbedding
      (fun y : Space => DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u (previous j) (unrotate y))
    rw [← h]
    apply integral_congr_ae
    filter_upwards with y
    change DyadicKernel.remainder k (x-rotate y) i j *
      DynamicVolume.source c u (previous j) (unrotate (rotate y)) = _
    rw [unrotate_rotate]
    have hxy : x-rotate y = rotate (unrotate x-y) := by
      change x - rotation y = rotation (rotation.symm x-y)
      simp
    rw [hxy, Packet06CyclicKernel.remainder_rotate]
  unfold Packet06AxialConvolution.potential
  simp_rw [hone]
  simp only [Fin.sum_univ_three, WeakCurl.previous]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

end OQ14.Packet06CyclicPotential
#print axioms OQ14.Packet06CyclicPotential.potential_rotate
