import FullChannelContinuous
import ModalVectorAngularSlices

/-! Rotation of general angular L² amplitudes into magnetic polarization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelMagnetic
open MeasureTheory SphereHarmonicBasis
open ComplexVectorSphere (embedVector)
abbrev Vector := ComplexVectorSphere.Vector
abbrev Ambient := ComplexVectorSphere.Ambient
open scoped ComplexInnerProductSpace

/-- Pointwise cross product in the Euclidean vector representation. -/
def crossVec (v w : Vector) : Vector :=
  (WithLp.equiv 2 (Fin 3 → ℂ)).symm (crossProduct (fun i => v i) (fun i => w i))

theorem crossVec_continuous : Continuous (fun p : Vector × Vector => crossVec p.1 p.2) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : Vector × Vector => p.1 1 * p.2 2 - p.1 2 * p.2 1)
    fun_prop
  · change Continuous (fun p : Vector × Vector => p.1 2 * p.2 0 - p.1 0 * p.2 2)
    fun_prop
  · change Continuous (fun p : Vector × Vector => p.1 0 * p.2 1 - p.1 1 * p.2 0)
    fun_prop

/-- Magnetic polarization density n cross F(n). -/
def rotationFunction (F : Ambient) (n : Sphere) : Vector := crossVec (embedVector (n : Maxwell.Space)) (F n)

theorem rotation_memLp (F : Ambient) : MemLp (rotationFunction F) 2 angularMeasure := by
  have hn : StronglyMeasurable (fun n : Sphere => embedVector (n : Maxwell.Space)) :=
    (embedVector.continuous.comp continuous_subtype_val).stronglyMeasurable
  have hf := Lp.stronglyMeasurable F
  have hm : AEStronglyMeasurable (rotationFunction F) angularMeasure :=
    (crossVec_continuous.comp_stronglyMeasurable (hn.prodMk hf)).aestronglyMeasurable
  apply (Lp.memLp F).of_le_mul (c := 6) hm
  filter_upwards with n
  have hnorm : ‖embedVector (n : Maxwell.Space)‖ = 1 := by
    rw [ModalVectorAngularSlices.embed_norm, AngularPower.sphere_norm]
  have hdir (j : Fin 3) : ‖embedVector (n : Maxwell.Space) j‖ ≤ 1 := by
    simpa [hnorm] using PiLp.norm_apply_le (embedVector (n : Maxwell.Space)) j
  have hsrc (j : Fin 3) : ‖F n j‖ ≤ ‖F n‖ := PiLp.norm_apply_le (F n) j
  have hc (j : Fin 3) : ‖rotationFunction F n j‖ ≤ 2 * ‖F n‖ := by
    change ‖crossProduct (fun i => embedVector (n : Maxwell.Space) i) (fun i => F n i) j‖ ≤ _
    exact ChannelScaledFields.cross_norm_le _ _ ‖F n‖ hdir hsrc j
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℂ) (rotationFunction F n)
  simp only [Fin.sum_univ_three] at hsq
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  nlinarith [sq_nonneg (‖rotationFunction F n 0‖ - 2*‖F n‖),
    sq_nonneg (‖rotationFunction F n 1‖ - 2*‖F n‖),
    sq_nonneg (‖rotationFunction F n 2‖ - 2*‖F n‖),
    norm_nonneg (rotationFunction F n), norm_nonneg (F n),
    norm_nonneg (rotationFunction F n 0), norm_nonneg (rotationFunction F n 1), norm_nonneg (rotationFunction F n 2)]

/-- Pointwise boundedness of cross-product polarization rotation. -/
theorem rotation_point_bound (F : Ambient) (n : Sphere) :
    ‖rotationFunction F n‖ ≤ 6 * ‖F n‖ := by
  have hnorm : ‖embedVector (n : Maxwell.Space)‖ = 1 := by
    rw [ModalVectorAngularSlices.embed_norm, AngularPower.sphere_norm]
  have hdir (j : Fin 3) : ‖embedVector (n : Maxwell.Space) j‖ ≤ 1 := by
    simpa [hnorm] using PiLp.norm_apply_le (embedVector (n : Maxwell.Space)) j
  have hsrc (j : Fin 3) : ‖F n j‖ ≤ ‖F n‖ := PiLp.norm_apply_le (F n) j
  have hc (j : Fin 3) : ‖rotationFunction F n j‖ ≤ 2 * ‖F n‖ := by
    change ‖crossProduct (fun i => embedVector (n : Maxwell.Space) i) (fun i => F n i) j‖ ≤ _
    exact ChannelScaledFields.cross_norm_le _ _ ‖F n‖ hdir hsrc j
  have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℂ) (rotationFunction F n)
  simp only [Fin.sum_univ_three] at hsq
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  nlinarith [sq_nonneg (‖rotationFunction F n 0‖ - 2*‖F n‖),
    sq_nonneg (‖rotationFunction F n 1‖ - 2*‖F n‖),
    sq_nonneg (‖rotationFunction F n 2‖ - 2*‖F n‖),
    norm_nonneg (rotationFunction F n), norm_nonneg (F n),
    norm_nonneg (rotationFunction F n 0), norm_nonneg (rotationFunction F n 1), norm_nonneg (rotationFunction F n 2)]
def rotation (F : Ambient) : Ambient := (rotation_memLp F).toLp (rotationFunction F)

theorem rotation_actual (F : Ambient) : (rotation F : Sphere → Vector) =ᵐ[angularMeasure] rotationFunction F :=
  (rotation_memLp F).coeFn_toLp

/-- Rotating any sphere amplitude gives a transverse amplitude almost everywhere. -/
theorem rotation_tangential (F : Ambient) : ComplexVectorSphere.IsTangential (rotation F) := by
  filter_upwards [rotation_actual F] with n hn
  rw [hn]
  simp [rotationFunction, crossVec, PiLp.inner_apply, RCLike.inner_apply,
    ComplexVectorSphere.embed_apply, Fin.sum_univ_three, cross_apply]
  ring

/-- Rotation is additive on angular L². -/
theorem rotation_add (F G : Ambient) : rotation (F+G) = rotation F + rotation G := by
  apply Lp.ext
  filter_upwards [rotation_actual (F+G), rotation_actual F, rotation_actual G,
    Lp.coeFn_add F G, Lp.coeFn_add (rotation F) (rotation G)] with n h1 h2 h3 h4 h5
  rw [h1, h5]
  simp only [Pi.add_apply, h2, h3, rotationFunction]
  rw [h4]
  ext j
  fin_cases j <;> simp [crossVec, cross_apply] <;> ring

/-- Rotation respects complex scaling on angular L². -/
theorem rotation_smul (z : ℂ) (F : Ambient) : rotation (z • F) = z • rotation F := by
  apply Lp.ext
  filter_upwards [rotation_actual (z • F), rotation_actual F,
    Lp.coeFn_smul z F, Lp.coeFn_smul z (rotation F)] with n h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.smul_apply, h2, rotationFunction]
  rw [h3]
  ext j
  fin_cases j <;> simp [crossVec, cross_apply] <;> ring

/-- The angular rotation has a uniform L² bound. -/
theorem rotation_norm (F : Ambient) : ‖rotation F‖ ≤ 6 * ‖F‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [rotation_actual F] with n hn
  rw [hn]
  exact rotation_point_bound F n

/-- The magnetic-polarization rotation is a bounded linear operator on angular L². -/
def rotationCLM : Ambient →L[ℂ] Ambient :=
  ({ toFun := rotation, map_add' := rotation_add, map_smul' := rotation_smul } : Ambient →ₗ[ℂ] Ambient).mkContinuous 6 rotation_norm

/-- Continuous negative cross-product rotation used in the Maxwell Herglotz magnetic field. -/
def magneticMap (A : C(Sphere, Vector)) : C(Sphere, Vector) where
  toFun n := -crossVec (embedVector (n : Maxwell.Space)) (A n)
  continuous_toFun := (crossVec_continuous.comp
    ((embedVector.continuous.comp continuous_subtype_val).prodMk A.continuous)).neg

/-- Magnetic polarization is pointwise transverse. -/
theorem magneticMap_tangent (A : C(Sphere, Vector)) (n : Sphere) :
    @inner ℂ Vector _ (TransversePlaneFields.normal n) (magneticMap A n) = 0 := by
  simp [magneticMap, TransversePlaneFields.normal, crossVec, PiLp.inner_apply, RCLike.inner_apply,
    ComplexVectorSphere.embed_apply, Fin.sum_univ_three, cross_apply]
  ring

/-- The L² rotation agrees with the ordinary pointwise rotation of continuous amplitudes. -/
theorem magneticMap_toLp (A : C(Sphere, Vector)) :
    ContinuousMap.toLp 2 angularMeasure ℂ (magneticMap A) =
      -rotation (ContinuousMap.toLp 2 angularMeasure ℂ A) := by
  apply Lp.ext
  filter_upwards [(magneticMap A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    A.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    rotation_actual (ContinuousMap.toLp 2 angularMeasure ℂ A),
    Lp.coeFn_neg (rotation (ContinuousMap.toLp 2 angularMeasure ℂ A))] with n h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.neg_apply, h3, rotationFunction, h2]
  rfl

/-- For continuous angular input the L² magnetic field is exactly the classical Herglotz magnetic field. -/
theorem magnetic_value_toLp (k : ℝ) (A : C(Sphere, Vector)) (x : Maxwell.Space) (i : Fin 3) :
    HerglotzAngularL2.value k x i (-rotation (ContinuousMap.toLp 2 angularMeasure ℂ A)) =
      AngularHerglotz.magnetic k (fun n j => A n j) x i := by
  rw [← magneticMap_toLp, HerglotzAngularL2.value_toLp k _ (magneticMap_tangent A)]
  rfl

/-- Actual magnetic Herglotz field of arbitrary square-integrable angular input. -/
def magnetic (k : ℝ) (F : Ambient) : Maxwell.Field := fun x i =>
  HerglotzAngularL2.value k x i (-rotation F)

/-- The magnetic field is continuous in space even for general angular L² data. -/
theorem magnetic_continuous (k : ℝ) (F : Ambient) (i : Fin 3) :
    Continuous (fun x => magnetic k F x i) := by
  apply FullChannelHerglotz.electric_continuous
  exact FullChannelFreeMap.transverse.neg_mem (rotation_tangential F)

/-- Magnetic fields depend uniformly on the angular L² amplitude. -/
theorem magnetic_difference_bound (k : ℝ) (F G : Ambient) (x : Maxwell.Space) (i : Fin 3) :
    ‖magnetic k F x i - magnetic k G x i‖ ≤
      (6 * HerglotzAngularL2.bound) * ‖F-G‖ := by
  have h := HerglotzAngularL2.value_difference_bound k x i (-rotation F) (-rotation G)
  have hm : rotation (F-G) = rotation F - rotation G := map_sub rotationCLM F G
  have hr : ‖-rotation F - -rotation G‖ ≤ 6 * ‖F-G‖ := by
    rw [show -rotation F - -rotation G = -(rotation (F-G)) by rw [hm]; abel, norm_neg]
    exact rotation_norm (F-G)
  exact h.trans ((mul_le_mul_of_nonneg_left hr HerglotzAngularL2.bound_nonnegative).trans_eq (by ring))

end OQ14.FullChannelMagnetic
#print axioms OQ14.FullChannelMagnetic.crossVec_continuous
#print axioms OQ14.FullChannelMagnetic.rotation_memLp
#print axioms OQ14.FullChannelMagnetic.rotation_actual

#print axioms OQ14.FullChannelMagnetic.rotation_tangential
#print axioms OQ14.FullChannelMagnetic.rotation_add
#print axioms OQ14.FullChannelMagnetic.rotation_smul

#print axioms OQ14.FullChannelMagnetic.rotation_point_bound
#print axioms OQ14.FullChannelMagnetic.rotation_norm

#print axioms OQ14.FullChannelMagnetic.magneticMap_tangent
#print axioms OQ14.FullChannelMagnetic.magneticMap_toLp
#print axioms OQ14.FullChannelMagnetic.magnetic_value_toLp

#print axioms OQ14.FullChannelMagnetic.magnetic_continuous
#print axioms OQ14.FullChannelMagnetic.magnetic_difference_bound
