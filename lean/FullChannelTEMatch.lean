import FullChannelHerglotz
import RestrictedTEInput
import ChannelScatteringMap

/-! Exact identification of finite TE electric waves with transverse Herglotz data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelTEMatch
open MeasureTheory Maxwell RestrictedTEIncoming SymmetricHarmonicJets
open scoped Topology
abbrev Sphere := SphereReactionKernel.Sphere
abbrev Idx := SymmetricHarmonicJets.Index

/-- The actual plane-wave density of a finite TE incident field. -/
def densityMap (A : Idx →₀ ℂ) : C(Sphere, ComplexVectorSphere.Vector) :=
  ⟨fun n => (WithLp.equiv 2 (Fin 3 → ℂ)).symm (RestrictedTEAmplitude.density A n),
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
      (RestrictedTEAmplitude.density_continuous A)⟩

theorem densityMap_transverse (A : Idx →₀ ℂ) (n : Sphere) :
    @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n) (densityMap A n) = 0 := by
  rw [FiniteAngularHerglotz.normal_inner_dot]
  exact RestrictedTEAmplitude.density_transverse A n

/-- The wave sign is negative in the Herglotz API because its kernel is wave(-k). -/
theorem electric_value (A : Idx →₀ ℂ) (x : Maxwell.Space) (i : Fin 3) :
    HerglotzAngularL2.value (-1) x i (ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (densityMap A)) =
      RestrictedTEPlaneLocal.electric A x i := by
  rw [HerglotzAngularL2.value_toLp (-1) (densityMap A) (densityMap_transverse A)]
  simpa only [AngularHerglotz.electric, SphereWaveCalculus.moment, neg_neg,
    densityMap, ContinuousMap.coe_mk] using (RestrictedTEAmplitude.electric_herglotz A x i).symm

/-- The square-integrable plane-wave density is transverse almost everywhere. -/
theorem density_transverse (A : Idx →₀ ℂ) : ComplexVectorSphere.IsTangential
    (ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (densityMap A)) := by
  filter_upwards [(densityMap A).coeFn_toLp (p := 2) (𝕜 := ℂ) SphereHarmonicBasis.angularMeasure] with n hn
  rw [hn]
  exact densityMap_transverse A n

/-- The general angular-input material datum exactly matches the established TE datum. -/
theorem datum_eq (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (A : Idx →₀ ℂ) :
    FullChannelHerglotz.datum (-1) c d
      (ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (densityMap A)) (density_transverse A) =
        RestrictedTEMaterial.datum c d A := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  filter_upwards [FullChannelHerglotz.datum_actual (-1) c d _ (density_transverse A) i,
    RestrictedTEMaterial.datum_actual c d A i] with x h1 h2
  rw [h1, h2, electric_value]

/-- The actual frequency-one volume inverse produces the same solution as the finite TE construction. -/
theorem solution_eq (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (A : Idx →₀ ℂ) :
    Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius)
      (FullChannelHerglotz.datum (-1) c d
        (ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (densityMap A)) (density_transverse A)) =
      ChannelScatteringMap.solLin c d A := by
  rw [datum_eq, ChannelScatteringMap.solLin_apply]

/-- Exact relationship between Herglotz plane-wave density and power-normalized incoming amplitude. -/
theorem input_eq_density (A : Idx →₀ ℂ) :
    RestrictedTEInput.input A =
      ((2 * Real.pi * Complex.I : ℂ) / (Real.sqrt 2 : ℂ)) •
        ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (densityMap A) := by
  have hm : RestrictedTEInput.amplitudeMap A = (2 * Real.pi * Complex.I : ℂ) • densityMap A := by
    ext n i
    rw [RestrictedTEInput.amplitudeMap_apply, RestrictedTEAmplitude.amplitude_eq]
    rfl
  change (1 / (Real.sqrt 2 : ℂ)) •
    ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (RestrictedTEInput.amplitudeMap A) = _
  rw [hm, map_smul, smul_smul]
  congr 1
  ring

/-- The normalized incoming angular amplitude reconstructs the incident electric wave
    with the exact plane-wave normalization factor. -/
theorem electric_from_input (A : Idx →₀ ℂ) (x : Maxwell.Space) (i : Fin 3) :
    HerglotzAngularL2.value (-1) x i (RestrictedTEInput.input A) =
      ((2 * Real.pi * Complex.I : ℂ) / (Real.sqrt 2 : ℂ)) * RestrictedTEPlaneLocal.electric A x i := by
  rw [input_eq_density, map_smul, electric_value]
  rfl

/-- The incident datum for a power-normalized incoming angular amplitude. The factor
    converts from incoming Hankel amplitude to plane-wave density. -/
def normalizedDatum (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F) : VectorFourier.VectorL2 :=
  ((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) • FullChannelHerglotz.datum (-1) c d F hF

/-- On the physical TE sector, the normalized datum exactly equals its actual material datum. -/
theorem normalized_datum_eq (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (A : Idx →₀ ℂ) : normalizedDatum c d (RestrictedTEInput.input A) (RestrictedTEInput.input_transverse A) =
      RestrictedTEMaterial.datum c d A := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (MeasureTheory.Lp.coeFn_smul ((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I))
      (FullChannelHerglotz.datum (-1) c d (RestrictedTEInput.input A) (RestrictedTEInput.input_transverse A)))
  filter_upwards [hs, FullChannelHerglotz.datum_actual (-1) c d _ (RestrictedTEInput.input_transverse A) i,
    RestrictedTEMaterial.datum_actual c d A i] with x hs h1 h2
  change (((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) •
    FullChannelHerglotz.datum (-1) c d (RestrictedTEInput.input A) (RestrictedTEInput.input_transverse A))
      (VectorFourier.coordinateMap x) i = _
  rw [hs]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [h1, h2, electric_from_input]
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : (Real.sqrt 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  field_simp
  ring

/-- Physical plane-wave electric field corresponding to a power-normalized incoming amplitude. -/
def normalizedElectric (F : ComplexVectorSphere.Ambient) : Maxwell.Field := fun x i =>
  ((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) * HerglotzAngularL2.value (-1) x i F

/-- The normalized incident field is the actual weighted datum used by the material volume equation. -/
theorem normalized_datum_actual (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F) (i : Fin 3) :
    (fun x => normalizedDatum c d F hF (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * normalizedElectric F x i := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (MeasureTheory.Lp.coeFn_smul ((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I))
      (FullChannelHerglotz.datum (-1) c d F hF))
  filter_upwards [hs, FullChannelHerglotz.datum_actual (-1) c d F hF i] with x hs h1
  change (((Real.sqrt 2 : ℂ) / (2 * Real.pi * Complex.I)) • FullChannelHerglotz.datum (-1) c d F hF)
      (VectorFourier.coordinateMap x) i = _
  rw [hs]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [h1]
  dsimp [normalizedElectric]
  ring

/-- Physical volume solution for any power-normalized transverse incoming L² wave. -/
def normalizedSolution (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F) : VectorFourier.VectorL2 :=
  Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius) (normalizedDatum c d F hF)

/-- The resulting general-input polarization satisfies the material constitutive relation. -/
theorem normalized_material_relation (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : ComplexVectorSphere.Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) (i : Fin 3) :
    DynamicVolume.source c (normalizedSolution c d F hF) i =ᵐ[volume] fun x =>
      (c.value (VectorFourier.coordinateMap x) : ℂ) *
        MaterialField.total c 1 (normalizedSolution c d F hF) (normalizedElectric F) x i := by
  apply MaterialField.material_relation c 1 d.radius _ _ _ d.ballZero (normalized_datum_actual c d F hF)
  exact congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L (normalizedDatum c d F hF))
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c 1 d.radius) hu)

/-- Power-normalized full outgoing amplitude: the free outgoing part plus the actual
    material-source radiation, with the physical half-power normalization. -/
def outputFromDatum (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (free : ComplexVectorSphere.Ambient) (datum : VectorFourier.VectorL2) : ComplexVectorSphere.Ambient :=
  free + (1 / (Real.sqrt 2 : ℂ)) •
    ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ
      (ChannelScatteringMap.farMap c d (Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius) datum))

/-- With the genuine outgoing Hankel part and Herglotz material datum, the full
    output is exactly the already established physical TE scattering map. -/
theorem output_eq (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (A : Idx →₀ ℂ) :
    outputFromDatum c d
      ((1 / (Real.sqrt 2 : ℂ)) • ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ
        (ChannelScatteringMap.outHankelMap A))
      (FullChannelHerglotz.datum (-1) c d
        (ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (densityMap A)) (density_transverse A)) =
      ChannelScatteringMap.scatterMap c d A := by
  unfold outputFromDatum ChannelScatteringMap.scatterMap ChannelScatteringMap.outCM
  rw [solution_eq]
  change (1 / (Real.sqrt 2 : ℂ)) • ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ
      (ChannelScatteringMap.outHankelMap A) +
    (1 / (Real.sqrt 2 : ℂ)) • ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ
      (ChannelScatteringMap.farMap c d (ChannelScatteringMap.solLin c d A)) =
    (1 / (Real.sqrt 2 : ℂ)) • ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ
      (ChannelScatteringMap.outHankelMap A + ChannelScatteringMap.farMap c d (ChannelScatteringMap.solLin c d A))
  rw [map_add, smul_add]

/-- The normalized general-input formula agrees with the complete finite-TE
    physical scattering output, including the √2 power normalization. -/
theorem normalized_output_eq (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (A : Idx →₀ ℂ) :
    outputFromDatum c d
      ((1 / (Real.sqrt 2 : ℂ)) • ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ
        (ChannelScatteringMap.outHankelMap A))
      (normalizedDatum c d (RestrictedTEInput.input A) (RestrictedTEInput.input_transverse A)) =
      ChannelScatteringMap.scatterMap c d A := by
  rw [normalized_datum_eq, ← datum_eq]
  exact output_eq c d A

end OQ14.FullChannelTEMatch
#print axioms OQ14.FullChannelTEMatch.densityMap_transverse
#print axioms OQ14.FullChannelTEMatch.electric_value


#print axioms OQ14.FullChannelTEMatch.density_transverse
#print axioms OQ14.FullChannelTEMatch.datum_eq
#print axioms OQ14.FullChannelTEMatch.solution_eq

#print axioms OQ14.FullChannelTEMatch.input_eq_density

#print axioms OQ14.FullChannelTEMatch.output_eq

#print axioms OQ14.FullChannelTEMatch.electric_from_input

#print axioms OQ14.FullChannelTEMatch.normalized_datum_eq

#print axioms OQ14.FullChannelTEMatch.normalized_output_eq

#print axioms OQ14.FullChannelTEMatch.normalized_datum_actual
#print axioms OQ14.FullChannelTEMatch.normalized_material_relation
