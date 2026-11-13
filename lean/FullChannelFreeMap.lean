import FullChannelTEMatch
import SphereAngularSymmetry
import ChannelAntipodalAmplitude

/-! The actual free full-output map on angular L², including antipodal reversal. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelFreeMap
open MeasureTheory Maxwell SphereHarmonicBasis

abbrev Ambient := ComplexVectorSphere.Ambient
abbrev Sphere := SphereHarmonicBasis.Sphere

def antipode : Sphere ≃ₜ Sphere :=
  SphereAngularSymmetry.sphereMap (LinearIsometryEquiv.neg ℝ : Maxwell.Space ≃ₗᵢ[ℝ] Maxwell.Space)

theorem antipode_preserving : MeasurePreserving antipode angularMeasure angularMeasure :=
  SphereAngularSymmetry.measurePreserving_sphereMap _

/-- The free outgoing angular amplitude is minus the incoming amplitude at the antipode. -/
def freeMap : Ambient →ₗ[ℂ] Ambient :=
  -(Lp.compMeasurePreservingₗᵢ ℂ antipode antipode_preserving).toLinearMap

theorem free_norm (F : Ambient) : ‖freeMap F‖ = ‖F‖ := by
  simp [freeMap]

theorem free_actual (F : Ambient) :
    (freeMap F : Sphere → ComplexVectorSphere.Vector) =ᵐ[angularMeasure]
      fun n => -F (antipode n) := by
  have hc := Lp.coeFn_compMeasurePreserving F antipode_preserving
  have hn := Lp.coeFn_neg ((Lp.compMeasurePreservingₗᵢ ℂ antipode antipode_preserving) F)
  filter_upwards [hc, hn] with n hc hn
  change freeMap F n = _
  change (-(Lp.compMeasurePreservingₗᵢ ℂ antipode antipode_preserving) F) n = _
  change ((Lp.compMeasurePreservingₗᵢ ℂ antipode antipode_preserving) F) n = F (antipode n) at hc
  rw [hn]
  simp only [Pi.neg_apply, hc]

/-- Antipodal free propagation preserves transverse polarizations. -/
theorem free_tangential (F : Ambient) (hF : ComplexVectorSphere.IsTangential F) :
    ComplexVectorSphere.IsTangential (freeMap F) := by
  have ht := antipode_preserving.quasiMeasurePreserving.ae hF
  filter_upwards [free_actual F, ht] with n hf ht
  rw [hf]
  have hn : (antipode n : Maxwell.Space) = -(n : Maxwell.Space) := rfl
  change inner (ComplexVectorSphere.embedVector (n : Maxwell.Space)) (-F (antipode n)) = 0
  have hnormal : ComplexVectorSphere.embedVector (antipode n : Maxwell.Space) =
      -ComplexVectorSphere.embedVector (n : Maxwell.Space) := by rw [hn, map_neg]
  rw [hnormal, inner_neg_left] at ht
  rw [inner_neg_right, neg_eq_zero]
  exact neg_eq_zero.mp ht

/-- The free map is exactly the outgoing Hankel wave of every finite TE input. -/
theorem free_on_TE (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    freeMap (RestrictedTEInput.input A) =
      (1 / (Real.sqrt 2 : ℂ)) • ContinuousMap.toLp 2 angularMeasure ℂ
        (ChannelScatteringMap.outHankelMap A) := by
  let a := (1 / (Real.sqrt 2 : ℂ))
  let g := ContinuousMap.toLp 2 angularMeasure ℂ (ChannelScatteringMap.outHankelMap A)
  have ho := (ChannelScatteringMap.outHankelMap A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure
  have hi := (RestrictedTEInput.amplitudeMap A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure
  have hi' := antipode_preserving.quasiMeasurePreserving.ae hi
  have hs := Lp.coeFn_smul a (RestrictedTEInput.rawInput A)
  have hs' := antipode_preserving.quasiMeasurePreserving.ae hs
  have ht := Lp.coeFn_smul a g
  apply Lp.ext
  filter_upwards [free_actual (RestrictedTEInput.input A), ho, hi', hs', ht] with n hf ho hi hs ht
  have he : antipode n = ChannelAntipodalAmplitude.negSphere n := by
    apply Subtype.ext
    rfl
  change RestrictedTEInput.rawInput A (antipode n) = RestrictedTEInput.amplitudeMap A (antipode n) at hi
  change RestrictedTEInput.input A (antipode n) = a • RestrictedTEInput.rawInput A (antipode n) at hs
  change g n = ChannelScatteringMap.outHankelMap A n at ho
  change (a • g) n = a • g n at ht
  rw [hf, hs, hi, ht, ho]
  ext j
  simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul]
  rw [ChannelScatteringMap.outHankelMap_apply, ChannelAntipodalAmplitude.aE_false_antipodal,
    ChannelUnitThroughput.aE_true_eq, ← he, RestrictedTEInput.amplitudeMap_apply]
  simp

/-- The physical incoming Hilbert sector consists of the transverse L² amplitudes. -/
def transverse : Submodule ℂ Ambient where
  carrier := {F | ComplexVectorSphere.IsTangential F}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero (E := ComplexVectorSphere.Vector) (p := 2) (μ := angularMeasure)] with n hn
    change _ = (0 : ComplexVectorSphere.Vector) at hn
    rw [hn, inner_zero_right]
  add_mem' := by
    intro F G hF hG
    filter_upwards [hF, hG, Lp.coeFn_add F G] with n hf hg h
    rw [h]
    change inner _ (F n + G n) = 0
    rw [inner_add_right, hf, hg, add_zero]
  smul_mem' := by
    intro z F hF
    filter_upwards [hF, Lp.coeFn_smul z F] with n hf h
    rw [h]
    change inner _ (z • F n) = 0
    rw [inner_smul_right, hf, mul_zero]

/-- The actual radiation amplitude is tangential on the full output sphere. -/
theorem radiated_tangential (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (u : VectorFourier.VectorL2) :
    ComplexVectorSphere.IsTangential
      (ContinuousMap.toLp 2 angularMeasure ℂ (ChannelScatteringMap.farMap c d u)) := by
  filter_upwards [(ChannelScatteringMap.farMap c d u).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hn
  rw [hn]
  change inner (TransversePlaneFields.normal n) (ChannelScatteringMap.farMap c d u n) = 0
  rw [FiniteAngularHerglotz.normal_inner_dot]
  have h := MaxwellFarField.amplitude_transverse 1 (DynamicVolume.source c u) (n : Maxwell.Space)
    (AngularPower.sphere_norm n)
  change Maxwell.dot (ConicalPlaneWaves.direction n)
    (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) (n : Maxwell.Space)) = 0
  have he : MaxwellRadiation.direction (n : Maxwell.Space) = ConicalPlaneWaves.direction n := by
    ext j
    simp [MaxwellRadiation.direction, GreenKernel.unitCoordinate, ConicalPlaneWaves.direction,
      AngularPower.sphere_norm n]
  rw [← he]
  exact h

/-- The physical incident datum is additive on transverse incoming waves. -/
theorem normalizedDatum_add (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F G : Ambient) (hF : ComplexVectorSphere.IsTangential F) (hG : ComplexVectorSphere.IsTangential G)
    (hFG : ComplexVectorSphere.IsTangential (F+G)) :
    FullChannelTEMatch.normalizedDatum c d (F+G) hFG =
      FullChannelTEMatch.normalizedDatum c d F hF + FullChannelTEMatch.normalizedDatum c d G hG := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (FullChannelTEMatch.normalizedDatum c d F hF) (FullChannelTEMatch.normalizedDatum c d G hG))
  filter_upwards [hs, FullChannelTEMatch.normalized_datum_actual c d (F+G) hFG i,
    FullChannelTEMatch.normalized_datum_actual c d F hF i,
    FullChannelTEMatch.normalized_datum_actual c d G hG i] with x hs h1 h2 h3
  rw [hs]
  simp only [Pi.add_apply, PiLp.add_apply]
  rw [h1, h2, h3]
  simp only [FullChannelTEMatch.normalizedElectric, map_add]
  ring

/-- The physical incident datum respects complex rescaling. -/
theorem normalizedDatum_smul (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (z : ℂ) (F : Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (hzF : ComplexVectorSphere.IsTangential (z • F)) :
    FullChannelTEMatch.normalizedDatum c d (z • F) hzF = z • FullChannelTEMatch.normalizedDatum c d F hF := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_smul z (FullChannelTEMatch.normalizedDatum c d F hF))
  filter_upwards [hs, FullChannelTEMatch.normalized_datum_actual c d (z • F) hzF i,
    FullChannelTEMatch.normalized_datum_actual c d F hF i] with x hs h1 h2
  rw [hs]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [h1, h2]
  simp only [FullChannelTEMatch.normalizedElectric, map_smul, smul_eq_mul]
  ring

/-- The exact normalized material datum is a complex-linear function of the transverse input. -/
def datumMap (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c) :
    transverse →ₗ[ℂ] VectorFourier.VectorL2 where
  toFun F := FullChannelTEMatch.normalizedDatum c d F.val F.property
  map_add' F G := normalizedDatum_add c d F.val G.val F.property G.property (F+G).property
  map_smul' z F := normalizedDatum_smul c d z F.val F.property (z • F).property

/-- Physical scattering restricted to the transverse incoming space is complex-linear. -/
def scatteringLinear (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c) :
    transverse →ₗ[ℂ] Ambient :=
  freeMap.comp (transverse.subtype) +
    (1 / (Real.sqrt 2 : ℂ)) •
      (ContinuousMap.toLp 2 angularMeasure ℂ).toLinearMap.comp
        ((ChannelScatteringMap.farMap c d).comp
          ((Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius)).toLinearMap.comp (datumMap c d)))

/-- Full physical angular output for an arbitrary tangential L² incoming amplitude:
    antipodal free propagation plus the outgoing field radiated by the actual volume solution. -/
def physicalScatter (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : Ambient) (hF : ComplexVectorSphere.IsTangential F) : Ambient :=
  FullChannelTEMatch.outputFromDatum c d (freeMap F) (FullChannelTEMatch.normalizedDatum c d F hF)

/-- The global formula restricts exactly to the previously constructed complete TE scattering map. -/
theorem physicalScatter_on_TE (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    physicalScatter c d (RestrictedTEInput.input A) (RestrictedTEInput.input_transverse A) =
      ChannelScatteringMap.scatterMap c d A := by
  unfold physicalScatter
  rw [free_on_TE]
  exact FullChannelTEMatch.normalized_output_eq c d A

/-- The complete global scattering formula maps transverse inputs to transverse outputs. -/
theorem scatteringLinear_tangential (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : transverse) : ComplexVectorSphere.IsTangential (scatteringLinear c d F) := by
  change freeMap F.val + (1 / (Real.sqrt 2 : ℂ)) •
    ContinuousMap.toLp 2 angularMeasure ℂ
      (ChannelScatteringMap.farMap c d
        (Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius) (datumMap c d F))) ∈ transverse
  exact transverse.add_mem (free_tangential F.val F.property)
    (transverse.smul_mem _ (radiated_tangential c d _))

/-- The linear map is exactly the physical free-plus-radiated construction. -/
theorem scatteringLinear_apply (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (F : transverse) : scatteringLinear c d F = physicalScatter c d F.val F.property := by
  rfl

/-- The linear full-input scattering map agrees with all existing TE scattering amplitudes. -/
theorem scatteringLinear_on_TE (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    scatteringLinear c d ⟨RestrictedTEInput.input A, RestrictedTEInput.input_transverse A⟩ =
      ChannelScatteringMap.scatterMap c d A := by
  rw [scatteringLinear_apply]
  exact physicalScatter_on_TE c d A

/-- The actual TE illumination as an element of the full transverse input space. -/
def teInput : (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ] transverse where
  toFun A := ⟨RestrictedTEInput.input A, RestrictedTEInput.input_transverse A⟩
  map_add' A B := Subtype.ext (map_add RestrictedTEInput.input A B)
  map_smul' z A := Subtype.ext (map_smul RestrictedTEInput.input z A)

/-- The entire restricted operator is the pullback of the global physical formula. -/
theorem scattering_comp_te (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c) :
    (scatteringLinear c d).comp teInput = ChannelScatteringMap.scatterMap c d := by
  apply LinearMap.ext
  intro A
  exact scatteringLinear_on_TE c d A

/-- An orthonormal N-family spans an N-dimensional subspace in the physical incoming Hilbert space. -/
theorem physical_span_finrank (N : ℕ) (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ)
    (horth : Orthonormal ℂ (fun j => RestrictedTEInput.input (A j))) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun j => RestrictedTEInput.input (A j)))) = N := by
  rw [finrank_span_eq_card horth.linearIndependent]
  simp


end OQ14.FullChannelFreeMap
#print axioms OQ14.FullChannelFreeMap.antipode_preserving
#print axioms OQ14.FullChannelFreeMap.free_norm
#print axioms OQ14.FullChannelFreeMap.free_actual

#print axioms OQ14.FullChannelFreeMap.free_on_TE

#print axioms OQ14.FullChannelFreeMap.physicalScatter_on_TE

#print axioms OQ14.FullChannelFreeMap.normalizedDatum_add

#print axioms OQ14.FullChannelFreeMap.normalizedDatum_smul

#print axioms OQ14.FullChannelFreeMap.scatteringLinear_apply
#print axioms OQ14.FullChannelFreeMap.scatteringLinear_on_TE

#print axioms OQ14.FullChannelFreeMap.scattering_comp_te
#print axioms OQ14.FullChannelFreeMap.physical_span_finrank


#print axioms OQ14.FullChannelFreeMap.free_tangential

#print axioms OQ14.FullChannelFreeMap.radiated_tangential

#print axioms OQ14.FullChannelFreeMap.scatteringLinear_tangential
