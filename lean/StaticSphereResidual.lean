import StaticSphereMaterial

/-! # Actual inverse residual and physical source error for a static sphere trial

The trial is identified with the existing material-weighted static inverse.
The comparison concerns the literal explicit parity-kernel volume block.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticSphereResidual

open MeasureTheory Metric Set StaticBallNewton StaticSphereMaterial ParityReactionVolume
open scoped Topology

theorem solution_residual {c : StaticCoefficient.Coefficient} (d : SupportData c)
    (k B : ℝ) (hsmall : perturbationBound d k B ≤ 1/2) (f v : VectorL2) :
    ‖ParityMaterialField.solution d k B f - v‖ ≤
      2 * ‖f - ParityMaterialField.block d k B v‖ := by
  have hu := explicitBlock_isUnit d k B (by linarith)
  have he : Ring.inverse (ParityMaterialField.block d k B)
      (ParityMaterialField.block d k B v) = v := by
    exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L v) (Ring.inverse_mul_cancel _ hu)
  have hd : ParityMaterialField.solution d k B f - v =
      Ring.inverse (ParityMaterialField.block d k B) (f-ParityMaterialField.block d k B v) := by
    rw [map_sub, he]
    rfl
  rw [hd]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
    (explicitBlock_inverse_le_two d k B hsmall) (norm_nonneg _))

theorem static_comparison {c : StaticCoefficient.Coefficient} (d : SupportData c)
    (k B : ℝ) (hsmall : perturbationBound d k B ≤ 1/2) (f f₀ v : VectorL2)
    (hv : StaticCoefficient.weightedBlock c v = f₀) :
    ‖ParityMaterialField.solution d k B f-v‖ ≤
      2 * (‖f-f₀‖ + perturbationBound d k B * ‖v‖) := by
  apply (solution_residual d k B hsmall f v).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  have he : f-ParityMaterialField.block d k B v =
      (f-f₀)+perturbation d k B v := by
    change f-(StaticCoefficient.weightedBlock c v-perturbation d k B v) = _
    rw [hv]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add_left
    ((ContinuousLinearMap.le_opNorm _ v).trans
      (mul_le_mul_of_nonneg_right (perturbation_norm d k B) (norm_nonneg v))) _)

def errorBound {χ : ℝ} {hχ : 0 ≤ χ} {c : Space} {R : ℝ}
    (d : SupportData (coefficient c R χ hχ)) (k B : ℝ) (f : VectorL2) (E : Vector) : ℝ :=
  2*(‖f-forcing c R χ E‖ + perturbationBound d k B*‖trial c R χ E‖)

theorem sphere_comparison (c : Space) (R : ℝ) (hR : 0 < R) (χ : ℝ) (hχ : 0 ≤ χ)
    (d : SupportData (coefficient c R χ hχ)) (k B : ℝ)
    (hsmall : perturbationBound d k B ≤ 1/2) (f : VectorL2) (E : Vector) :
    ‖ParityMaterialField.solution d k B f-trial c R χ E‖ ≤ errorBound d k B f E :=
  static_comparison d k B hsmall f (forcing c R χ E) (trial c R χ E)
    (weightedBlock_trial c R hR χ hχ E)

theorem physical_L2_error (c : Space) (R : ℝ) (hR : 0 < R) (χ : ℝ) (hχ : 0 ≤ χ)
    (d : SupportData (coefficient c R χ hχ)) (k B : ℝ)
    (hsmall : perturbationBound d k B ≤ 1/2) (f : VectorL2) (E : Vector) :
    ‖StaticCoefficient.sqrtMultiplier (coefficient c R χ hχ) (ParityMaterialField.solution d k B f) -
      StaticBallCentered.source c R (StaticSpherePolarization.polarization χ E)‖ ≤
        Real.sqrt χ * errorBound d k B f E := by
  rw [← physical_source c R χ hχ E, ← map_sub]
  exact (StaticCoefficient.applySqrt_norm _ _).trans
    (mul_le_mul_of_nonneg_left (sphere_comparison c R hR χ hχ d k B hsmall f E)
      (Real.sqrt_nonneg _))

theorem trial_source_ae (c : Space) (R χ : ℝ) (hχ : 0 ≤ χ) (E : Vector) (i : Fin 3) :
    DynamicVolume.source (coefficient c R χ hχ) (trial c R χ E) i =ᵐ[volume]
      (ball c R).indicator (fun _ => StaticSpherePolarization.polarization χ E i) := by
  have hp := StaticNewton.material_source_ae (coefficient c R χ hχ) (trial c R χ E) i
  rw [physical_source c R χ hχ E] at hp
  have hc := NewtonL2.physicalCoordinate_ae
    (StaticBallCentered.source c R (StaticSpherePolarization.polarization χ E)) i
  exact hp.symm.trans (hc.trans (StaticBallCentered.source_ae c R _ i))

theorem physical_L1_error (c : Space) (R : ℝ) (hR : 0 < R) (χ : ℝ) (hχ : 0 ≤ χ)
    (d : SupportData (coefficient c R χ hχ)) (k B : ℝ)
    (hsmall : perturbationBound d k B ≤ 1/2) (f : VectorL2) (E : Vector) (i : Fin 3) :
    (∫ x, ‖DynamicVolume.source (coefficient c R χ hχ) (ParityMaterialField.solution d k B f) i x -
      (ball c R).indicator (fun _ => StaticSpherePolarization.polarization χ E i) x‖) ≤
        (Real.sqrt χ * errorBound d k B f E) * Real.sqrt (volume.real d.carrier) := by
  let u := ParityMaterialField.solution d k B f
  let v := trial c R χ E
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_sub u v)
  have he : (∫ x, ‖DynamicVolume.source (coefficient c R χ hχ) u i x -
      (ball c R).indicator (fun _ => StaticSpherePolarization.polarization χ E i) x‖) =
      ∫ x, ‖DynamicConvolution.component i
        (StaticCoefficient.sqrtMultiplier (coefficient c R χ hχ) (u-v)) x‖ := by
    apply integral_congr_ae
    filter_upwards [hs, trial_source_ae c R χ hχ E i,
      StaticNewton.material_source_ae (coefficient c R χ hχ) (u-v) i] with x hs ht hp
    rw [DynamicConvolution.component_apply, hp, ← ht]
    unfold DynamicVolume.source
    rw [hs]
    simp only [Pi.sub_apply, PiLp.sub_apply, mul_sub]
    rfl
  rw [he]
  exact (BoundedMaterialKernel.source_mass d (u-v) i).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (sphere_comparison c R hR χ hχ d k B hsmall f E)
        (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

end OQ14.StaticSphereResidual

#print axioms OQ14.StaticSphereResidual.solution_residual
#print axioms OQ14.StaticSphereResidual.static_comparison
#print axioms OQ14.StaticSphereResidual.sphere_comparison
#print axioms OQ14.StaticSphereResidual.physical_L2_error
#print axioms OQ14.StaticSphereResidual.trial_source_ae
#print axioms OQ14.StaticSphereResidual.physical_L1_error
