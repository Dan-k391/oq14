import DilationL2
import DilationKernels
import MaterialField
import MaterialMaxwell
import SourcePairedPlaneIdentification
import ShellInclusionVolume

/-! Field-level dilation identities: the frequency-`k` fields of the material solution.

For `k > 0` let `scaleField k F x = k • F (k • x)`, `scaleCoeff k c` the coefficient `ξ ↦ c.value (k • ξ)` and
`dilate k` the dilation operator on `VectorL2` (`DilationL2`).  The frequency-one material fields of `(c, u)`,
rescaled by `scaleField k`, are the frequency-`k` material fields of `(scaleCoeff k c, dilate k u)`:

* `scattered_dilate`, `total_dilate`: the `L2` scattered and total electric fields, almost everywhere;
* `totalMagnetic_dilate`: the pointwise total magnetic field, at every point;
* `scaleCoeff_add`: the dilation of a coefficient commutes with the sum of coefficients;
* `isDatum_dilate`: the weighted datum of a field is dilated to the weighted datum of the dilated field.

Scalar factors: the Newton term carries the factor `k` of `physicalCoordinate_dilate`, the remainder term the factor
`k` of `DilationKernels.electric_remainder_scale`, the magnetic term the factor `k` of `DilationKernels.magnetic_scale`;
all three agree with `scaleField`. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FrequencyFieldResponse
open MeasureTheory OQ14.Maxwell
open OQ14.FrequencyScalingMaxwell (scaleField scaleCoeff)

/-! ### Plumbing -/

theorem response_congr_ae (q ρ ρ' : Space → ℂ) (h : ρ =ᵐ[volume] ρ') (x : Space) :
    KernelConvolution.response q ρ x = KernelConvolution.response q ρ' x := by
  unfold KernelConvolution.response
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem magnetic_congr_ae (k : ℝ) (ρ τ : Fin 3 → Space → ℂ) (h : ∀ j, ρ j =ᵐ[volume] τ j) (x : Space)
    (i : Fin 3) : MagneticResponse.magnetic k ρ x i = MagneticResponse.magnetic k τ x i := by
  unfold MagneticResponse.magnetic
  rw [response_congr_ae _ _ _ (h (WeakCurl.previous i)) x, response_congr_ae _ _ _ (h (WeakCurl.next i)) x]

/-- `scaleField` respects almost everywhere equality of a coordinate. -/
theorem scaleField_congr_ae (k : ℝ) (hk : 0 < k) (F G : Field) (i : Fin 3)
    (h : (fun x => F x i) =ᵐ[volume] fun x => G x i) :
    (fun x => scaleField k F x i) =ᵐ[volume] fun x => scaleField k G x i := by
  filter_upwards [DilationL2.ae_smul_space k hk.ne' (P := fun x => F x i = G x i) h] with x hx
  rw [OQ14.FrequencyScalingMaxwell.scaleField_apply, OQ14.FrequencyScalingMaxwell.scaleField_apply]
  rw [hx]

/-! ### The scattered and total electric fields -/

/-- **`scattered_dilate`.**  The frequency-one scattered field of `(c, u)`, rescaled, is the frequency-`k` scattered
field of `(scaleCoeff k c, dilate k u)`, almost everywhere. -/
theorem scattered_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2)
    (i : Fin 3) :
    (fun x => scaleField k (MaterialField.scattered c 1 u) x i) =ᵐ[volume]
      fun x => MaterialField.scattered (scaleCoeff k c) k (DilationL2.dilate k u) x i := by
  have hN := DilationL2.physicalCoordinate_dilate k hk
    (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u)) i
  filter_upwards [hN] with x hx
  have hnewton : NewtonL2.newtonOperator (DilationL2.dilate k (StaticCoefficient.sqrtMultiplier c u)) =
      DilationL2.dilate k (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u)) :=
    congrFun (congrArg DFunLike.coe (DilationL2.newtonOperator_comp_dilate k hk))
      (StaticCoefficient.sqrtMultiplier c u)
  have hsrc : ∀ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder k z i j)
      (DynamicVolume.source (scaleCoeff k c) (DilationL2.dilate k u) j) x =
      KernelConvolution.response (fun z => DyadicKernel.remainder k z i j)
        (fun y => (k : ℂ) * DynamicVolume.source c u j (k • y)) x := fun j =>
    response_congr_ae _ _ _ (DilationL2.source_dilate k hk c u j) x
  rw [OQ14.FrequencyScalingMaxwell.scaleField_apply]
  unfold MaterialField.scattered FieldResponse.electric
  rw [DilationL2.sqrtMultiplier_dilate k hk c u, hnewton, hx, Finset.sum_congr rfl (fun j _ => hsrc j),
    DilationKernels.electric_remainder_scale k hk (fun j => DynamicVolume.source c u j) x i]
  rw [mul_add]

/-- **`total_dilate`.**  The same for the total electric field with the incident field rescaled. -/
theorem total_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2)
    (inc : Field) (i : Fin 3) :
    (fun x => scaleField k (MaterialField.total c 1 u inc) x i) =ᵐ[volume]
      fun x => MaterialField.total (scaleCoeff k c) k (DilationL2.dilate k u) (scaleField k inc) x i := by
  filter_upwards [scattered_dilate k hk c u i] with x hx
  have h : (k : ℂ) * MaterialField.scattered c 1 u (k • x) i =
      MaterialField.scattered (scaleCoeff k c) k (DilationL2.dilate k u) x i := hx
  change (k : ℂ) * (inc (k • x) i + MaterialField.scattered c 1 u (k • x) i) =
    scaleField k inc x i + MaterialField.scattered (scaleCoeff k c) k (DilationL2.dilate k u) x i
  rw [← h, OQ14.FrequencyScalingMaxwell.scaleField_apply]
  ring

/-! ### The total magnetic field -/

/-- **`totalMagnetic_dilate`.**  The frequency-one total magnetic field of `(c, u)`, rescaled, is the frequency-`k`
total magnetic field of `(scaleCoeff k c, dilate k u)` at every point. -/
theorem totalMagnetic_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient)
    (u : VectorFourier.VectorL2) (inc : Field) (x : Space) (i : Fin 3) :
    scaleField k (MaterialMaxwell.totalMagnetic c 1 u inc) x i =
      MaterialMaxwell.totalMagnetic (scaleCoeff k c) k (DilationL2.dilate k u) (scaleField k inc) x i := by
  rw [OQ14.FrequencyScalingMaxwell.scaleField_apply]
  unfold MaterialMaxwell.totalMagnetic
  rw [magnetic_congr_ae k _ (fun j y => (k : ℂ) * DynamicVolume.source c u j (k • y))
    (fun j => DilationL2.source_dilate k hk c u j) x i,
    DilationKernels.magnetic_scale k hk (fun j => DynamicVolume.source c u j) x i,
    OQ14.FrequencyScalingMaxwell.scaleField_apply]
  ring

/-! ### Coefficients and data -/

/-- Dilation of coefficients commutes with the sum of coefficients. -/
theorem scaleCoeff_add (k : ℝ) (c₁ c₂ : StaticCoefficient.Coefficient) :
    scaleCoeff k (ShellInclusionVolume.add c₁ c₂) =
      ShellInclusionVolume.add (scaleCoeff k c₁) (scaleCoeff k c₂) := rfl

theorem dielectric_scaleCoeff_add (k : ℝ) (c₁ c₂ : StaticCoefficient.Coefficient) (x : Space) :
    MaterialMaxwell.dielectric (ShellInclusionVolume.add (scaleCoeff k c₁) (scaleCoeff k c₂)) x =
      MaterialMaxwell.dielectric (ShellInclusionVolume.add c₁ c₂) (k • x) := by
  rw [← scaleCoeff_add]
  exact OQ14.FrequencyScalingMaxwell.dielectric_scaleCoeff k _ x

/-- **`isDatum_dilate`.**  The dilation of a weighted datum is the weighted datum of the dilated field. -/
theorem isDatum_dilate (k : ℝ) (hk : 0 < k) (c : StaticCoefficient.Coefficient) (F : Field)
    (h : VectorFourier.VectorL2) (hd : SourcePairedPlaneIdentification.IsDatum c F h) :
    SourcePairedPlaneIdentification.IsDatum (scaleCoeff k c) (scaleField k F) (DilationL2.dilate k h) := by
  intro i
  filter_upwards [VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (DilationL2.dilate_ae k hk h),
    DilationL2.ae_smul_space k hk.ne'
      (P := fun x => h (VectorFourier.coordinateMap x) i =
        (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * F x i) (hd i)] with x h1 h2
  rw [h1]
  rw [OQ14.FrequencyScalingMaxwell.scaleField_apply]
  have e : (Real.sqrt ((scaleCoeff k c).value (VectorFourier.coordinateMap x)) : ℂ) =
      (Real.sqrt (c.value (VectorFourier.coordinateMap (k • x))) : ℂ) := rfl
  rw [e]
  change (k : ℂ) * h (k • VectorFourier.coordinateMap x) i = _
  have h3 : h (k • VectorFourier.coordinateMap x) i =
      (Real.sqrt (c.value (VectorFourier.coordinateMap (k • x))) : ℂ) * F (k • x) i := h2
  rw [h3]
  ring

end OQ14.FrequencyFieldResponse

#print axioms OQ14.FrequencyFieldResponse.response_congr_ae
#print axioms OQ14.FrequencyFieldResponse.magnetic_congr_ae
#print axioms OQ14.FrequencyFieldResponse.scaleField_congr_ae
#print axioms OQ14.FrequencyFieldResponse.scattered_dilate
#print axioms OQ14.FrequencyFieldResponse.total_dilate
#print axioms OQ14.FrequencyFieldResponse.totalMagnetic_dilate
#print axioms OQ14.FrequencyFieldResponse.scaleCoeff_add
#print axioms OQ14.FrequencyFieldResponse.dielectric_scaleCoeff_add
#print axioms OQ14.FrequencyFieldResponse.isDatum_dilate
