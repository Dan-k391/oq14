import FullChannelBoundedDatum

/-! Source-mass bounds for the full-angle radiated amplitude. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelFarBound
open MeasureTheory Maxwell

/-- Every physical source component has an L¹ mass bounded by its weighted L² norm. -/
theorem source_mass_bound (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (u : VectorFourier.VectorL2) (j : Fin 3) :
    (∫ x, ‖DynamicVolume.source c u j x‖) ≤
      (Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier) := by
  have ha := (StaticNewton.material_source_ae c u j).symm
  have he : (∫ x, ‖DynamicVolume.source c u j x‖) =
      ∫ x, ‖DynamicConvolution.component j (StaticCoefficient.sqrtMultiplier c u) x‖ := by
    apply integral_congr_ae
    exact ha.mono (fun x hx => congrArg norm hx)
  rw [he]
  exact BoundedMaterialKernel.source_mass d u j

/-- Every scalar far amplitude has a uniform direction-independent L² source bound. -/
theorem scalar_far_bound (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (u : VectorFourier.VectorL2) (j : Fin 3) (n : Maxwell.Space) :
    ‖ScalarFarField.amplitude 1 (DynamicVolume.source c u j) n‖ ≤
      ((Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier)) / (4 * Real.pi) := by
  have hp : 0 < 4 * Real.pi := by positivity
  have hk (x : Maxwell.Space) :
      ‖Complex.exp (-Complex.I * (1 : ℝ) * (inner n x : ℝ)) / (4 * Real.pi : ℂ)‖ = (4 * Real.pi)⁻¹ := by
    have hn : (-Complex.I * (1 : ℝ) * (inner n x : ℝ) : ℂ).re = 0 := by simp
    have hd : ‖(4 * Real.pi : ℂ)‖ = 4 * Real.pi := by
      rw [show (4 * Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    rw [norm_div, Complex.norm_exp, hn, Real.exp_zero, hd, one_div]
  unfold ScalarFarField.amplitude
  calc
    ‖∫ x, DynamicVolume.source c u j x * (Complex.exp (-Complex.I * (1 : ℝ) * (inner n x : ℝ)) / (4 * Real.pi : ℂ))‖
        ≤ ∫ x, ‖DynamicVolume.source c u j x * (Complex.exp (-Complex.I * (1 : ℝ) * (inner n x : ℝ)) / (4 * Real.pi : ℂ))‖ := norm_integral_le_integral_norm _
    _ = (∫ x, ‖DynamicVolume.source c u j x‖) / (4 * Real.pi) := by
      have he : (fun x => ‖DynamicVolume.source c u j x *
          (Complex.exp (-Complex.I * (1 : ℝ) * (inner n x : ℝ)) / (4 * Real.pi : ℂ))‖) =
          fun x => ‖DynamicVolume.source c u j x‖ * (4 * Real.pi)⁻¹ := by
        funext x
        rw [norm_mul, hk x]
      rw [he, integral_mul_const, div_eq_mul_inv]
    _ ≤ _ := div_le_div_of_nonneg_right (source_mass_bound c d u j) hp.le

/-- Each component of the actual radiated electric amplitude is uniformly bounded. -/
theorem electric_far_component_bound (c : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData c) (u : VectorFourier.VectorL2)
    (n : Maxwell.Space) (i : Fin 3) :
    ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n i‖ ≤
      6 * (((Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier)) / (4 * Real.pi)) := by
  let B : ℝ := ((Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier)) / (4 * Real.pi)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change ‖∑ j : Fin 3, ((1 : ℂ)^2 * DyadicRadiation.transverse n i j *
    ScalarFarField.amplitude 1 (DynamicVolume.source c u j) n)‖ ≤ 6 * B
  calc
    _ ≤ ∑ j : Fin 3, ‖(1 : ℂ)^2 * DyadicRadiation.transverse n i j *
      ScalarFarField.amplitude 1 (DynamicVolume.source c u j) n‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, 2 * B := by
      apply Finset.sum_le_sum
      intro j _
      simp only [one_pow, one_mul, norm_mul]
      exact mul_le_mul (DyadicRadiation.transverse_norm_bound n i j)
        (scalar_far_bound c d u j n) (norm_nonneg _) (by norm_num)
    _ = 6 * B := by simp [Fin.sum_univ_three]; ring

/-- Uniform vector norm bound for the actual radiated field on the sphere. -/
theorem electric_far_vector_bound (c : StaticCoefficient.Coefficient)
    (d : BoundedMaterialKernel.SupportData c) (u : VectorFourier.VectorL2) (n : Maxwell.Space) :
    ‖ChannelScatteringMap.toVec (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n)‖ ≤
      18 * (((Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier)) / (4 * Real.pi)) := by
  let B : ℝ := ((Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier)) / (4 * Real.pi)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h0 := electric_far_component_bound c d u n 0
  have h1 := electric_far_component_bound c d u n 1
  have h2 := electric_far_component_bound c d u n 2
  change ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 0‖ ≤ 6 * B at h0
  change ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 1‖ ≤ 6 * B at h1
  change ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 2‖ ≤ 6 * B at h2
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℂ) (ChannelScatteringMap.toVec
    (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n))
  simp only [Fin.sum_univ_three] at hn
  change ‖ChannelScatteringMap.toVec (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n)‖ ^ 2 =
    ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 0‖ ^ 2 +
    ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 1‖ ^ 2 +
    ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 2‖ ^ 2 at hn
  have hb0 : ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 0‖ ^ 2 ≤ (6*B)^2 := by
    nlinarith [norm_nonneg (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 0)]
  have hb1 : ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 1‖ ^ 2 ≤ (6*B)^2 := by
    nlinarith [norm_nonneg (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 1)]
  have hb2 : ‖MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 2‖ ^ 2 ≤ (6*B)^2 := by
    nlinarith [norm_nonneg (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n 2)]
  change ‖ChannelScatteringMap.toVec (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n)‖ ≤ 18*B
  nlinarith [norm_nonneg (ChannelScatteringMap.toVec (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) n))]

/-- The full angular L² norm of the radiated amplitude is bounded by the volume L² norm. -/
theorem farMap_bound (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (u : VectorFourier.VectorL2) :
    ‖ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (ChannelScatteringMap.farMap c d u)‖ ≤
      (((measureUnivNNReal SphereHarmonicBasis.angularMeasure : ℝ) ^ ((2 : ENNReal).toReal⁻¹)) *
        (18 * Real.sqrt c.bound * Real.sqrt (volume.real d.carrier) / (4 * Real.pi))) * ‖u‖ := by
  let B : ℝ := 18 * (((Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier)) / (4 * Real.pi))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have h := Lp.norm_le_of_ae_bound
    (f := ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (ChannelScatteringMap.farMap c d u)) hB
    (((ChannelScatteringMap.farMap c d u).coeFn_toLp (p := 2) (𝕜 := ℂ)
      SphereHarmonicBasis.angularMeasure).mono (fun n hn => by
        rw [hn]
        exact electric_far_vector_bound c d u (n : Maxwell.Space)))
  exact h.trans_eq (by dsimp [B]; ring)

/-- The actual volume-source radiation map is bounded on the complete output sphere. -/
def farCLM (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c) :
    VectorFourier.VectorL2 →L[ℂ] ComplexVectorSphere.Ambient :=
  ((ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ).toLinearMap.comp
    (ChannelScatteringMap.farMap c d)).mkContinuous
      (((measureUnivNNReal SphereHarmonicBasis.angularMeasure : ℝ) ^ ((2 : ENNReal).toReal⁻¹)) *
        (18 * Real.sqrt c.bound * Real.sqrt (volume.real d.carrier) / (4 * Real.pi))) (farMap_bound c d)

end OQ14.FullChannelFarBound
#print axioms OQ14.FullChannelFarBound.source_mass_bound

#print axioms OQ14.FullChannelFarBound.scalar_far_bound

#print axioms OQ14.FullChannelFarBound.electric_far_component_bound

#print axioms OQ14.FullChannelFarBound.electric_far_vector_bound

#print axioms OQ14.FullChannelFarBound.farMap_bound
