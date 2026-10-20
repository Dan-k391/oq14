import SmallParityInclusions
import MaterialField

/-! # Literal self-consistent material solution for the explicit parity kernel

The actual inverse produces the unique volume unknown. Its source equals
chi times the incident plus free plus explicit parity reaction field.
This is not an identification with a finite radial-background Green field.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ParityMaterialField

open MeasureTheory Metric DynamicConvolution ParityReactionVolume
open scoped BigOperators

abbrev Field := Maxwell.Field

def reaction (c : Coefficient) (electric : Bool) (k : ℝ) (u : VectorL2) : Field :=
  fun x i => ∑ j : Fin 3, ∫ y, SphereReactionKernel.reaction electric k x y i j *
    DynamicVolume.source c u j y

def scattered (c : Coefficient) (k B : ℝ) (u : VectorL2) : Field :=
  fun x i => MaterialField.scattered c k u x i +
    ((B^2-1 : ℝ) : ℂ) * reaction c true k u x i +
    ((B⁻¹^2-1 : ℝ) : ℂ) * reaction c false k u x i

def total (c : Coefficient) (k B : ℝ) (u : VectorL2) (incident : Field) : Field :=
  fun x i => incident x i + scattered c k B u x i

def block {c : Coefficient} (d : SupportData c) (k B : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  StaticCoefficient.weightedBlock c - perturbation d k B

theorem block_eq {c : Coefficient} (d : SupportData c) (k B : ℝ) :
    block d k B = DynamicVolume.volumeBlock c k d.radius -
      ((B^2-1 : ℝ) : ℂ) • ParityReactionVolume.operator d true k -
      ((B⁻¹^2-1 : ℝ) : ℂ) • ParityReactionVolume.operator d false k := by
  unfold block perturbation DynamicVolume.volumeBlock
  rw [StaticNewton.volumeBlock_eq]
  abel

theorem block_actual {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (u : VectorL2) (i : Fin 3) :
    (fun x => block d k B u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => u (VectorFourier.coordinateMap x) i -
        (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * scattered c k B u x i := by
  let ze : ℂ := ((B^2-1 : ℝ) : ℂ)
  let zm : ℂ := ((B⁻¹^2-1 : ℝ) : ℂ)
  let v := DynamicVolume.volumeBlock c k d.radius u
  let e := ParityReactionVolume.operator d true k u
  let m := ParityReactionVolume.operator d false k u
  have heq : block d k B u = v - ze • e - zm • m := by
    rw [block_eq]
    rfl
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_sub (v-ze • e) (zm • m))
  have ht := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_sub v (ze • e))
  have he := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul ze e)
  have hm := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul zm m)
  filter_upwards [hs, ht, he, hm,
    DynamicVolume.volumeBlock_actual c u k d.radius d.ballZero i,
    MaterialField.scattered_actual c k u i,
    ParityReactionVolume.operator_actual d true k u i,
    ParityReactionVolume.operator_actual d false k u i] with x hs ht he hm hv hf her hmr
  rw [heq, hs]
  simp only [Pi.sub_apply, ht, he, hm, Pi.smul_apply, smul_eq_mul]
  change v (VectorFourier.coordinateMap x) i - ze * e (VectorFourier.coordinateMap x) i -
    zm * m (VectorFourier.coordinateMap x) i = _
  change v (VectorFourier.coordinateMap x) i = _ at hv
  change e (VectorFourier.coordinateMap x) i = _ at her
  change m (VectorFourier.coordinateMap x) i = _ at hmr
  rw [hv, her, hmr, ← hf]
  unfold scattered reaction ze zm
  ring

def solution {c : Coefficient} (d : SupportData c) (k B : ℝ) (f : VectorL2) : VectorL2 :=
  Ring.inverse (block d k B) f

theorem solution_equation {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (hsmall : perturbationBound d k B < 1) (f : VectorL2) :
    block d k B (solution d k B f) = f := by
  exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f)
    (Ring.mul_inverse_cancel (block d k B) (explicitBlock_isUnit d k B hsmall))

theorem solution_unique {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (hsmall : perturbationBound d k B < 1) (f u : VectorL2)
    (hsol : block d k B u = f) : u = solution d k B f :=
  (ContinuousLinearMap.isUnit_iff_bijective.mp (explicitBlock_isUnit d k B hsmall)).1
    (hsol.trans (solution_equation d k B hsmall f).symm)

theorem solution_norm {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (hsmall : perturbationBound d k B ≤ 1/2) (f : VectorL2) :
    ‖solution d k B f‖ ≤ 2 * ‖f‖ :=
  (ContinuousLinearMap.le_opNorm _ f).trans (mul_le_mul_of_nonneg_right
    (explicitBlock_inverse_le_two d k B hsmall) (norm_nonneg _))

/-- Actual polarization equals susceptibility times the actual explicit-kernel
total field. The forcing datum is the actual weighted incident field. -/
theorem material_relation {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (u f : VectorL2) (incident : Field)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * incident x i)
    (hsol : block d k B u = f) (i : Fin 3) :
    DynamicVolume.source c u i =ᵐ[volume] fun x =>
      (c.value (VectorFourier.coordinateMap x) : ℂ) * total c k B u incident x i := by
  filter_upwards [block_actual d k B u i, hincident i] with x hx hi
  rw [hsol, hi] at hx
  have hp : (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)^2 =
      (c.value (VectorFourier.coordinateMap x) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (c.nonnegative (VectorFourier.coordinateMap x))
  unfold DynamicVolume.source total
  rw [← hp]
  linear_combination -(Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * hx

theorem solution_material_relation {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (hsmall : perturbationBound d k B < 1) (f : VectorL2) (incident : Field)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * incident x i)
    (i : Fin 3) :
    DynamicVolume.source c (solution d k B f) i =ᵐ[volume] fun x =>
      (c.value (VectorFourier.coordinateMap x) : ℂ) *
        total c k B (solution d k B f) incident x i :=
  material_relation d k B _ f incident hincident (solution_equation d k B hsmall f) i

theorem polarization_norm {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (hsmall : perturbationBound d k B ≤ 1/2) (f : VectorL2) :
    ‖StaticCoefficient.sqrtMultiplier c (solution d k B f)‖ ≤
      2 * Real.sqrt c.bound * ‖f‖ := by
  exact (StaticCoefficient.applySqrt_norm c _).trans
    ((mul_le_mul_of_nonneg_left (solution_norm d k B hsmall f)
      (Real.sqrt_nonneg _)).trans_eq (by ring))

theorem source_mass {c : Coefficient} (d : SupportData c) (k B : ℝ)
    (hsmall : perturbationBound d k B ≤ 1/2) (f : VectorL2) (i : Fin 3) :
    (∫ x, ‖DynamicVolume.source c (solution d k B f) i x‖) ≤
      (2 * Real.sqrt c.bound * Real.sqrt (volume.real d.carrier)) * ‖f‖ := by
  have he : (∫ x, ‖DynamicVolume.source c (solution d k B f) i x‖) =
      ∫ x, ‖component i (StaticCoefficient.sqrtMultiplier c (solution d k B f)) x‖ := by
    apply integral_congr_ae
    filter_upwards [StaticNewton.material_source_ae c (solution d k B f) i] with x hx
    rw [component_apply, hx]
    rfl
  rw [he]
  exact (BoundedMaterialKernel.source_mass d _ i).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (solution_norm d k B hsmall f) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)).trans_eq (by ring))

end OQ14.ParityMaterialField

#print axioms OQ14.ParityMaterialField.block_eq
#print axioms OQ14.ParityMaterialField.block_actual
#print axioms OQ14.ParityMaterialField.solution_equation
#print axioms OQ14.ParityMaterialField.solution_unique
#print axioms OQ14.ParityMaterialField.solution_norm
#print axioms OQ14.ParityMaterialField.material_relation
#print axioms OQ14.ParityMaterialField.solution_material_relation
#print axioms OQ14.ParityMaterialField.polarization_norm
#print axioms OQ14.ParityMaterialField.source_mass
