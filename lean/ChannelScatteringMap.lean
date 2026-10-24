import ChannelMaterialThroughput

/-! The scattering map of the actual material device on the finite input space, as a linear map into the L2
amplitude space, and its isometry.

For a coefficient `c` with support data `d`, `solLin c d A = Ring.inverse (volumeBlock c 1 d.radius) (datum c d A)` is
complex-linear in the finite TE coefficient vector `A`, and the amplitude of the complete field
`A ↦ aE A false + electricAmplitude 1 (source c (solLin c d A))` is complex-linear as well (the far amplitude is an
integral of the source, so almost-everywhere linearity of `u ↦ source c u` suffices).  `scatterMap c d` is the
normalized amplitude in `ComplexVectorSphere.Ambient = L2 (sphere, C^3)`, normalized like `RestrictedTEInput.input`,
and `scatterMap_norm : ‖scatterMap c d A‖ = ‖input A‖` when the volume block is a unit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.ChannelScatteringMap
open Filter MeasureTheory Metric Topology OQ14.Maxwell OQ14.ChannelScaledFields OQ14.ChannelFarFluxExpansion
  OQ14.ChannelUnitThroughput OQ14.ChannelMaterialThroughput
abbrev Idx := SymmetricHarmonicJets.Index
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Sphere := SphereReactionKernel.Sphere
abbrev AVec := ComplexVectorSphere.Vector
abbrev Ambient := ComplexVectorSphere.Ambient

/-! ### Linearity of the far amplitude in the source -/

theorem amplitude_integrable (k : ℝ) (ρ : Space → ℂ) (hρ : Integrable ρ) (n : Space) :
    Integrable (fun y => ρ y * (Complex.exp (-Complex.I * k * (inner n y : ℝ)) / (4 * Real.pi))) := by
  have hK : Continuous (fun y : Space => Complex.exp (-Complex.I * k * (inner n y : ℝ)) / (4 * Real.pi)) := by
    fun_prop
  have h := hρ.bdd_mul hK.aestronglyMeasurable ⟨(‖(4 * Real.pi : ℂ)‖)⁻¹, fun y => by
    rw [norm_div, Complex.norm_exp]
    have h0 : (-Complex.I * (k : ℂ) * ((inner n y : ℝ) : ℂ)).re = 0 := by simp
    rw [h0, Real.exp_zero, one_div]⟩
  exact h.congr (Eventually.of_forall (fun y => mul_comm _ _))

theorem amplitude_add (k : ℝ) (ρ σ : Space → ℂ) (hρ : Integrable ρ) (hσ : Integrable σ) (n : Space) :
    ScalarFarField.amplitude k (fun y => ρ y + σ y) n =
      ScalarFarField.amplitude k ρ n + ScalarFarField.amplitude k σ n := by
  unfold ScalarFarField.amplitude
  simp_rw [add_mul]
  exact integral_add (amplitude_integrable k ρ hρ n) (amplitude_integrable k σ hσ n)

theorem amplitude_smul (k : ℝ) (z : ℂ) (ρ : Space → ℂ) (n : Space) :
    ScalarFarField.amplitude k (fun y => z * ρ y) n = z * ScalarFarField.amplitude k ρ n := by
  unfold ScalarFarField.amplitude
  simp_rw [mul_assoc]
  exact integral_const_mul z _

theorem amplitude_congr_ae (k : ℝ) (ρ σ : Space → ℂ) (h : ρ =ᵐ[volume] σ) (n : Space) :
    ScalarFarField.amplitude k ρ n = ScalarFarField.amplitude k σ n := by
  unfold ScalarFarField.amplitude
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem electricAmplitude_add (k : ℝ) (ρ σ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hσ : ∀ j, Integrable (σ j)) (n : Space) :
    MaxwellFarField.electricAmplitude k (fun j y => ρ j y + σ j y) n =
      MaxwellFarField.electricAmplitude k ρ n + MaxwellFarField.electricAmplitude k σ n := by
  ext i
  simp only [MaxwellFarField.electricAmplitude, MaxwellFarField.potentialAmplitude, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [amplitude_add k (ρ j) (σ j) (hρ j) (hσ j)]
  ring

theorem electricAmplitude_smul (k : ℝ) (z : ℂ) (ρ : Fin 3 → Space → ℂ) (n : Space) :
    MaxwellFarField.electricAmplitude k (fun j y => z * ρ j y) n = z • MaxwellFarField.electricAmplitude k ρ n := by
  ext i
  simp only [MaxwellFarField.electricAmplitude, MaxwellFarField.potentialAmplitude, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [amplitude_smul k z (ρ j) n]
  ring

theorem electricAmplitude_congr_ae (k : ℝ) (ρ σ : Fin 3 → Space → ℂ) (h : ∀ j, ρ j =ᵐ[volume] σ j) (n : Space) :
    MaxwellFarField.electricAmplitude k ρ n = MaxwellFarField.electricAmplitude k σ n := by
  ext i
  simp only [MaxwellFarField.electricAmplitude, MaxwellFarField.potentialAmplitude]
  apply Finset.sum_congr rfl
  intro j _
  rw [amplitude_congr_ae k (ρ j) (σ j) (h j) n]

theorem source_add_ae (c : Coefficient) (u v : VectorL2) (j : Fin 3) :
    DynamicVolume.source c (u + v) j =ᵐ[volume]
      fun y => DynamicVolume.source c u j y + DynamicVolume.source c v j y := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_add u v)
  filter_upwards [h] with y hy
  unfold DynamicVolume.source
  rw [hy]
  simp only [Pi.add_apply, PiLp.add_apply]
  ring

theorem source_smul_ae (c : Coefficient) (z : ℂ) (u : VectorL2) (j : Fin 3) :
    DynamicVolume.source c (z • u) j =ᵐ[volume] fun y => z * DynamicVolume.source c u j y := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul z u)
  filter_upwards [h] with y hy
  unfold DynamicVolume.source
  rw [hy]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-! ### The far amplitude map and the outgoing Hankel amplitude map -/

/-- Conversion of a vector to the Euclidean space of the L2 amplitude space. -/
def toVec (v : Vector) : AVec := (WithLp.equiv 2 (Fin 3 → ℂ)).symm v

/-- The far amplitude of the field radiated by the source of `u`, as a continuous map on the sphere. -/
def farMap (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) : VectorL2 →ₗ[ℂ] C(Sphere, AVec) where
  toFun u := ⟨fun n => toVec (MaxwellFarField.electricAmplitude 1 (DynamicVolume.source c u) (n : Space)),
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
      (OQ14.AngularPower.electric_amplitude_continuous 1 (DynamicVolume.source c u)
        (DynamicVolume.source_integrable c u d.radius d.ballZero))⟩
  map_add' u v := by
    ext n j
    have hs := DynamicVolume.source_integrable c u d.radius d.ballZero
    have ht := DynamicVolume.source_integrable c v d.radius d.ballZero
    have h1 := electricAmplitude_congr_ae 1 (DynamicVolume.source c (u + v))
      (fun j y => DynamicVolume.source c u j y + DynamicVolume.source c v j y) (source_add_ae c u v) (n : Space)
    have h2 := electricAmplitude_add 1 (DynamicVolume.source c u) (DynamicVolume.source c v) hs ht (n : Space)
    have h3 := congrFun (h1.trans h2) j
    simpa [toVec] using h3
  map_smul' z u := by
    ext n j
    have h1 := electricAmplitude_congr_ae 1 (DynamicVolume.source c (z • u))
      (fun j y => z * DynamicVolume.source c u j y) (source_smul_ae c z u) (n : Space)
    have h2 := electricAmplitude_smul 1 z (DynamicVolume.source c u) (n : Space)
    have h3 := congrFun (h1.trans h2) j
    simpa [toVec] using h3

/-- The outgoing Hankel amplitude of the incident finite TE field, as a column of a linear combination. -/
def outColumn (q : Idx) : C(Sphere, AVec) :=
  (((4 * Real.pi : ℂ) * Complex.I ^ q.val.1) * RegularTEIncoming.coefficient q.val.1 false / 2) •
    RestrictedTEInput.angularMap q

/-- The outgoing Hankel amplitude of the incident field as a linear map of the coefficient vector. -/
def outHankelMap : (Idx →₀ ℂ) →ₗ[ℂ] C(Sphere, AVec) := Finsupp.linearCombination ℂ outColumn

theorem outHankelMap_apply (A : Idx →₀ ℂ) (n : Sphere) (j : Fin 3) : outHankelMap A n j = aE A false n j := by
  have hs (s : Finset Idx) (F : Idx → AVec) : (∑ q ∈ s, F q) j = ∑ q ∈ s, F q j :=
    map_sum (EuclideanSpace.proj j : AVec →L[ℂ] ℂ) F s
  simp only [outHankelMap, Finsupp.linearCombination_apply, Finsupp.sum, ContinuousMap.sum_apply,
    ContinuousMap.coe_smul, Pi.smul_apply, Finset.sum_apply, hs, PiLp.smul_apply, smul_eq_mul, outColumn, aE,
    tau, RestrictedTEInput.angularMap, RestrictedTEIncoming.coefficient]
  apply Finset.sum_congr rfl
  intro q _
  change A q * ((((4 * Real.pi : ℂ) * Complex.I ^ q.val.1) * RegularTEIncoming.coefficient q.val.1 false / 2) *
      DebyeRadialTrace.angularToroidal (RestrictedTEIncoming.polynomial q) n j) =
    (A q * ((4 * Real.pi : ℂ) * Complex.I ^ q.val.1)) * (RegularTEIncoming.coefficient q.val.1 false / 2) *
      DebyeRadialTrace.angularToroidal (RestrictedTEIncoming.polynomial q) n j
  ring

/-! ### The scattering map -/

/-- The volume solution as a complex-linear function of the incident coefficient vector. -/
def solLin (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) : (Idx →₀ ℂ) →ₗ[ℂ] VectorL2 :=
  (Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius)).toLinearMap.comp (RestrictedTEDatumLinear.datumMap c d)

theorem solLin_apply (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (A : Idx →₀ ℂ) :
    solLin c d A = Ring.inverse (DynamicVolume.volumeBlock c 1 d.radius) (RestrictedTEMaterial.datum c d A) := rfl

/-- The amplitude of the complete field as a linear map into continuous maps on the sphere. -/
def outCM (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) : (Idx →₀ ℂ) →ₗ[ℂ] C(Sphere, AVec) :=
  outHankelMap + (farMap c d).comp (solLin c d)

theorem outCM_apply (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (A : Idx →₀ ℂ) (n : Sphere)
    (j : Fin 3) : outCM c d A n j = outAmplitude A (DynamicVolume.source c (solLin c d A)) n j := by
  change outHankelMap A n j + farMap c d (solLin c d A) n j = _
  rw [outHankelMap_apply]
  rfl

/-- The scattering map of the material device on the finite input space, with values in the L2 amplitude space,
normalized like `RestrictedTEInput.input`. -/
def scatterMap (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) : (Idx →₀ ℂ) →ₗ[ℂ] Ambient :=
  (1 / (Real.sqrt 2 : ℂ)) •
    (ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ).toLinearMap.comp (outCM c d)

theorem toLp_norm_sq (F : C(Sphere, AVec)) :
    ‖ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ F‖ ^ 2 =
      ∫ n : Sphere, energy (fun j => F n j) ∂SphereReactionKernel.surface := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  have hEq : (∫ n : Sphere, (inner (ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ F n)
        (ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ F n) : ℂ) ∂SphereReactionKernel.surface) =
      ∫ n : Sphere, (energy (fun j => F n j) : ℂ) ∂SphereReactionKernel.surface := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) SphereReactionKernel.surface F] with n hn
    rw [hn]
    simp only [PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_three, energy, Complex.ofReal_add,
      ← Complex.mul_conj]
  change (∫ n : Sphere, (inner (ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ F n)
        (ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ F n) : ℂ) ∂SphereReactionKernel.surface).re = _
  rw [hEq, integral_complex_ofReal]
  simp

theorem scatterMap_norm_sq (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (hU : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) (A : Idx →₀ ℂ) :
    ‖scatterMap c d A‖ ^ 2 = ‖RestrictedTEInput.input A‖ ^ 2 := by
  have h := material_unit_throughput_of_isUnit c d hU A
  have hn : ‖scatterMap c d A‖ ^ 2 =
      (1 / 2 : ℝ) * ∫ n : Sphere, energy (fun j => outCM c d A n j) ∂SphereReactionKernel.surface := by
    change ‖(1 / (Real.sqrt 2 : ℂ)) • ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ (outCM c d A)‖ ^ 2 = _
    rw [norm_smul, mul_pow, toLp_norm_sq]
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have he := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    congr 1
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, div_pow, he]
    norm_num
  rw [hn, ← h]
  have hint : (∫ n : Sphere, energy (fun j => outCM c d A n j) ∂SphereReactionKernel.surface) =
      ∫ n : Sphere, energy (outAmplitude A (DynamicVolume.source c (solLin c d A)) n)
        ∂OQ14.AngularPower.angularMeasure := by
    apply integral_congr_ae
    filter_upwards with n
    unfold energy
    simp only [outCM_apply]
  rw [hint, solLin_apply]
  ring

theorem scatterMap_norm (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (hU : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) (A : Idx →₀ ℂ) :
    ‖scatterMap c d A‖ = ‖RestrictedTEInput.input A‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (scatterMap_norm_sq c d hU A)

/-- The scattering map preserves inner products of finite TE inputs. -/
theorem scatterMap_inner (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (hU : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) (A B : Idx →₀ ℂ) :
    (inner (scatterMap c d A) (scatterMap c d B) : ℂ) =
      (inner (RestrictedTEInput.input A) (RestrictedTEInput.input B) : ℂ) := by
  rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (scatterMap c d A) (scatterMap c d B),
    inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (RestrictedTEInput.input A) (RestrictedTEInput.input B)]
  have h1 : ‖scatterMap c d A + scatterMap c d B‖ = ‖RestrictedTEInput.input A + RestrictedTEInput.input B‖ := by
    rw [← map_add, ← map_add, scatterMap_norm c d hU]
  have h2 : ‖scatterMap c d A - scatterMap c d B‖ = ‖RestrictedTEInput.input A - RestrictedTEInput.input B‖ := by
    rw [← map_sub, ← map_sub, scatterMap_norm c d hU]
  have h3 : ‖scatterMap c d A - (RCLike.I : ℂ) • scatterMap c d B‖ =
      ‖RestrictedTEInput.input A - (RCLike.I : ℂ) • RestrictedTEInput.input B‖ := by
    rw [← map_smul, ← map_smul, ← map_sub, ← map_sub, scatterMap_norm c d hU]
  have h4 : ‖scatterMap c d A + (RCLike.I : ℂ) • scatterMap c d B‖ =
      ‖RestrictedTEInput.input A + (RCLike.I : ℂ) • RestrictedTEInput.input B‖ := by
    rw [← map_smul, ← map_smul, ← map_add, ← map_add, scatterMap_norm c d hU]
  rw [h1, h2, h3, h4]

/-- Orthonormal finite TE inputs are mapped to orthonormal outputs. -/
theorem scatterMap_orthonormal (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (hU : IsUnit (DynamicVolume.volumeBlock c 1 d.radius)) {κ : Type*} [DecidableEq κ] (A : κ → Idx →₀ ℂ)
    (h : Orthonormal ℂ (fun k => RestrictedTEInput.input (A k))) :
    Orthonormal ℂ (fun k => scatterMap c d (A k)) := by
  rw [orthonormal_iff_ite] at h ⊢
  intro i j
  rw [scatterMap_inner c d hU]
  exact h i j

/-! ### The paired shells plus inclusion -/

/-- The scattering map of the paired-shell-plus-inclusion device at shell index `r` is an isometry of the finite
input space whenever the effective inclusion block is a unit. -/
theorem paired_scatterMap_norm (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x) = 0)
    (hE : IsUnit (DynamicVolume.volumeBlock ci 1 b -
      ShellInclusionReaction.reaction (SourcePairedInclusion.shell q hq n r) ci 1
        (SourcePairedInclusion.data q hq n r).X))
    (A : Idx →₀ ℂ) :
    ‖scatterMap (pairedCoeff q hq n r ci) (pairedSupport q hq n r ci b hb hci) A‖ =
      ‖RestrictedTEInput.input A‖ :=
  scatterMap_norm (pairedCoeff q hq n r ci) (pairedSupport q hq n r ci b hb hci)
    (SourcePairedInclusion.combined_isUnit_of_effective q hq n r ci b hb hci hE) A

/-- For a fixed finite inclusion with a unit limiting effective block, for all large shell indices the scattering
map of the paired device is an inner-product preserving linear map of the finite input space. -/
theorem paired_scatterMap_eventually (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0 < b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b)
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb)) :
    ∀ᶠ r : ℕ in atTop, ∃ hbR : b ≤ (SourcePairedInclusion.data q hq n r).R,
      ∀ A B : Idx →₀ ℂ,
        (inner (scatterMap (pairedCoeff q hq n r ci)
            (pairedSupport q hq n r ci b hbR (SourcePairedReduction.inclusion_vanish ci d b hcar)) A)
          (scatterMap (pairedCoeff q hq n r ci)
            (pairedSupport q hq n r ci b hbR (SourcePairedReduction.inclusion_vanish ci d b hcar)) B) : ℂ) =
          (inner (RestrictedTEInput.input A) (RestrictedTEInput.input B) : ℂ) := by
  filter_upwards [SourcePairedReduction.eventually_effective_isUnit q hq n ci d b hb hcar hL,
    SourcePairedReduction.eventually_inner_radius q hq n b] with r hE hbR
  exact ⟨hbR.le, fun A B => scatterMap_inner (pairedCoeff q hq n r ci)
    (pairedSupport q hq n r ci b hbR.le (SourcePairedReduction.inclusion_vanish ci d b hcar))
    (SourcePairedInclusion.combined_isUnit_of_effective q hq n r ci b hbR.le
      (SourcePairedReduction.inclusion_vanish ci d b hcar) hE) A B⟩

end OQ14.ChannelScatteringMap
#print axioms OQ14.ChannelScatteringMap.amplitude_integrable
#print axioms OQ14.ChannelScatteringMap.amplitude_add
#print axioms OQ14.ChannelScatteringMap.amplitude_smul
#print axioms OQ14.ChannelScatteringMap.amplitude_congr_ae
#print axioms OQ14.ChannelScatteringMap.electricAmplitude_add
#print axioms OQ14.ChannelScatteringMap.electricAmplitude_smul
#print axioms OQ14.ChannelScatteringMap.electricAmplitude_congr_ae
#print axioms OQ14.ChannelScatteringMap.source_add_ae
#print axioms OQ14.ChannelScatteringMap.source_smul_ae
#print axioms OQ14.ChannelScatteringMap.outHankelMap_apply
#print axioms OQ14.ChannelScatteringMap.solLin_apply
#print axioms OQ14.ChannelScatteringMap.outCM_apply
#print axioms OQ14.ChannelScatteringMap.toLp_norm_sq
#print axioms OQ14.ChannelScatteringMap.scatterMap_norm_sq
#print axioms OQ14.ChannelScatteringMap.scatterMap_norm
#print axioms OQ14.ChannelScatteringMap.scatterMap_inner
#print axioms OQ14.ChannelScatteringMap.scatterMap_orthonormal
#print axioms OQ14.ChannelScatteringMap.paired_scatterMap_norm
#print axioms OQ14.ChannelScatteringMap.paired_scatterMap_eventually
