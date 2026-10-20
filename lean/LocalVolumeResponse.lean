import DynamicConvolution
import FieldResponse

/-! # Actual locally L2 electric volume response

Every observation ball has a genuine global L2 representative obtained by an
exact kernel cutoff beyond the sum of the observation and source radii.
The literal field used in the distributional source equation agrees with that
representative on the observation ball.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.LocalVolumeResponse

open MeasureTheory Metric OQ14.Maxwell

abbrev VectorL2 := VectorFourier.VectorL2

theorem kernel_source_eq (k R S : ℝ) (ρ : Space → ℂ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (i j : Fin 3)
    (x y : Space) (hx : x ∈ closedBall 0 R) :
    DynamicConvolution.kernel k (R+S) i j (x-y) * ρ y =
      DyadicKernel.remainder k (x-y) i j * ρ y := by
  by_cases hy : y ∈ closedBall (0 : Space) S
  · have hxy : x-y ∈ closedBall (0 : Space) (R+S) := by
      simp only [mem_closedBall, dist_zero_right] at hx hy ⊢
      exact (norm_sub_le _ _).trans (add_le_add hx hy)
    simp [DynamicConvolution.kernel, hxy]
  · simp [hc y hy]

theorem truncated_convolution (k T : ℝ) (F : VectorL2) (ρ : Space → ℂ)
    (j : Fin 3)
    (hF : (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ)
    (i : Fin 3) (x : Space) :
    HeatFourier.convolution (DynamicConvolution.kernel k T i j)
      (DynamicConvolution.component j F) x =
      ∫ y, DynamicConvolution.kernel k T i j (x-y) * ρ y := by
  change MeasureTheory.convolution (DynamicConvolution.kernel k T i j)
    (DynamicConvolution.component j F) (ContinuousLinearMap.mul ℂ ℂ) volume x = _
  rw [MeasureTheory.convolution_mul_swap]
  apply integral_congr_ae
  filter_upwards [hF] with y hy
  rw [DynamicConvolution.component_apply, hy]

theorem dynamic_ae_on_ball (k R S : ℝ) (F : VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) :
    (fun x => DynamicConvolution.operator k (R+S) F
      (VectorFourier.coordinateMap x) i) =ᵐ[volume.restrict (closedBall 0 R)]
      fun x => ∑ j, KernelConvolution.response
        (fun z => DyadicKernel.remainder k z i j) (ρ j) x := by
  have hd := DynamicConvolution.operator_ae_convolution k (R+S) F
    (fun j => (hρ j).congr (hF j).symm) i
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_closedBall] with x hx hxb
  rw [hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [truncated_convolution k (R+S) F (ρ j) j (hF j) i x]
  unfold KernelConvolution.response
  apply integral_congr_ae
  filter_upwards with y
  rw [kernel_source_eq k R S (ρ j) (hc j) i j x y hxb, mul_comm]

def localRepresentative (k R S : ℝ) (F : VectorL2) : VectorL2 :=
  NewtonL2.newtonOperator F + DynamicConvolution.operator k (R+S) F

theorem localRepresentative_norm (k R S : ℝ) (hT : 0 ≤ R+S) (F : VectorL2) :
    ‖localRepresentative k R S F‖ ≤
      (1 + 9 * DynamicConvolution.entryMass k (R+S)) * ‖F‖ := by
  apply (norm_add_le _ _).trans
  have hn := ContinuousLinearMap.le_opNorm NewtonL2.newtonOperator F
  have hnn := NewtonL2.newtonOperator_norm_le
  calc
    _ ≤ 1 * ‖F‖ + (9 * DynamicConvolution.entryMass k (R+S)) * ‖F‖ :=
      add_le_add (hn.trans (mul_le_mul_of_nonneg_right hnn (norm_nonneg _)))
        (DynamicConvolution.operator_norm k (R+S) hT F)
    _ = _ := by ring

theorem electric_ae_on_ball (k R S : ℝ) (F : VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) :
    (NewtonL2.physicalCoordinate (localRepresentative k R S F) i : Space → ℂ)
      =ᵐ[volume.restrict (closedBall 0 R)]
        fun x => FieldResponse.electric k F ρ x i := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (NewtonL2.newtonOperator F) (DynamicConvolution.operator k (R+S) F))
  filter_upwards [
    ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae (localRepresentative k R S F) i),
    ae_restrict_of_ae hs,
    ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae (NewtonL2.newtonOperator F) i),
    dynamic_ae_on_ball k R S F ρ hρ hc hF i] with x hx hs hn hd
  rw [hx]
  change (NewtonL2.newtonOperator F + DynamicConvolution.operator k (R+S) F)
    (VectorFourier.coordinateMap x) i = _
  rw [hs]
  change NewtonL2.newtonOperator F (VectorFourier.coordinateMap x) i +
    DynamicConvolution.operator k (R+S) F (VectorFourier.coordinateMap x) i = _
  rw [← hn, hd]
  rfl

theorem electric_memLp_ball (k R S : ℝ) (F : VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) :
    MemLp (fun x => FieldResponse.electric k F ρ x i) 2
      (volume.restrict (closedBall 0 R)) :=
  ((Lp.memLp (NewtonL2.physicalCoordinate (localRepresentative k R S F) i)).restrict
    (closedBall 0 R)).ae_eq (electric_ae_on_ball k R S F ρ hρ hc hF i)

theorem electric_locallyIntegrable (k S : ℝ) (F : VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) : LocallyIntegrable (fun x => FieldResponse.electric k F ρ x i) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_ne_top
  have hi : IntegrableOn (fun x => FieldResponse.electric k F ρ x i) (closedBall 0 R) :=
    (electric_memLp_ball k R S F ρ hρ hc hF i).integrable
      (by norm_num : (1 : ENNReal) ≤ 2)
  exact hi.mono_set hR

end OQ14.LocalVolumeResponse

#print axioms OQ14.LocalVolumeResponse.kernel_source_eq
#print axioms OQ14.LocalVolumeResponse.truncated_convolution
#print axioms OQ14.LocalVolumeResponse.dynamic_ae_on_ball
#print axioms OQ14.LocalVolumeResponse.localRepresentative_norm
#print axioms OQ14.LocalVolumeResponse.electric_ae_on_ball
#print axioms OQ14.LocalVolumeResponse.electric_memLp_ball
#print axioms OQ14.LocalVolumeResponse.electric_locallyIntegrable
