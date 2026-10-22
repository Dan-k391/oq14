import PlaneMaxwellFields
import SphereMagneticKernel

/-! Genuine separated source column integrals and coherent cross-product identities. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PointSourceColumns
open MeasureTheory Metric Set PlaneSourceKernel
open SphereMagneticKernel (magneticDyadic)
open Maxwell (Vector conjugate)
open WeakCurl (next previous)
open scoped ComplexConjugate Topology

private theorem conjugate_integrable {f : Maxwell.Space → ℂ} (hf : Integrable f) :
    Integrable (fun y => conj (f y)) :=
  Complex.conjCLE.toContinuousLinearMap.integrable_comp hf

private theorem gradient_integrable (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (i j : Fin 3) :
    Integrable (fun y => ρ j y*GreenKernel.phiGradient k (MaxwellPlaneTail.planePoint q-y) i) :=
  response_plane_integrable _ (KernelGradient.gradient_measurable k i)
    (fun x hx => (KernelGradient.gradient_differentiableAt k i x hx).continuousAt) R d hd ρ hρ q j

theorem electric_integrable (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (i j : Fin 3) :
    Integrable (fun y => ρ j y*DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) i j) :=
  response_plane_integrable _ (dyadic_measurable k i j)
    (fun x hx => ExteriorContinuity.dyadic_continuousAt k i j x hx) R d hd ρ hρ q j

theorem magnetic_integrable (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (i j : Fin 3) :
    Integrable (fun y => ρ j y*magneticDyadic k (MaxwellPlaneTail.planePoint q-y) i j) := by
  apply (((gradient_integrable k R d hd ρ hρ q (next i) j).mul_const (if previous i=j then 1 else 0)).sub
    ((gradient_integrable k R d hd ρ hρ q (previous i) j).mul_const (if next i=j then 1 else 0))).const_mul
      (-(Complex.I*(k : ℂ))) |>.congr
  filter_upwards with y
  simp only [Pi.sub_apply]
  unfold magneticDyadic
  ring

private theorem magnetic_response_column (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (i j : Fin 3) :
    (∫ y, ρ j y*magneticDyadic k (MaxwellPlaneTail.planePoint q-y) i j) =
      -(Complex.I*(k : ℂ))*(KernelConvolution.response
        (fun z => GreenKernel.phiGradient k z (next i)) (ρ j) (MaxwellPlaneTail.planePoint q)*
          (if previous i=j then 1 else 0)-KernelConvolution.response
        (fun z => GreenKernel.phiGradient k z (previous i)) (ρ j) (MaxwellPlaneTail.planePoint q)*
          (if next i=j then 1 else 0)) := by
  have he : (fun y => ρ j y*magneticDyadic k (MaxwellPlaneTail.planePoint q-y) i j) =
      (fun y => -(Complex.I*(k : ℂ))*(
        (ρ j y*GreenKernel.phiGradient k (MaxwellPlaneTail.planePoint q-y) (next i))*(if previous i=j then 1 else 0)-
        (ρ j y*GreenKernel.phiGradient k (MaxwellPlaneTail.planePoint q-y) (previous i))*(if next i=j then 1 else 0))) := by
    funext y
    unfold magneticDyadic
    ring
  rw [he, integral_const_mul,
    integral_sub ((gradient_integrable k R d hd ρ hρ q (next i) j).mul_const _)
      ((gradient_integrable k R d hd ρ hρ q (previous i) j).mul_const _), integral_mul_const, integral_mul_const]
  rfl

theorem magnetic_column_sum (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y, ρ j y*magneticDyadic k (MaxwellPlaneTail.planePoint q-y) i j) =
      MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) i := by
  simp_rw [magnetic_response_column k R d hd ρ hρ q]
  fin_cases i <;> simp [Fin.sum_univ_three, next, previous, MagneticResponse.magnetic, Fin.ext_iff] <;> ring

theorem electric_cross_columns (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (v : Vector) :
    crossProduct (ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q)) (conjugate v) 2 =
      ∑ j : Fin 3, ∫ y, ρ j y*crossProduct
        (fun i => DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) i j) (conjugate v) 2 := by
  change (∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic k z 0 j) (ρ j)
      (MaxwellPlaneTail.planePoint q))*star (v 1)-
    (∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic k z 1 j) (ρ j)
      (MaxwellPlaneTail.planePoint q))*star (v 0)=_
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold KernelConvolution.response
  rw [← integral_mul_const, ← integral_mul_const,
    ← integral_sub ((electric_integrable k R d hd ρ hρ q 0 j).mul_const _)
      ((electric_integrable k R d hd ρ hρ q 1 j).mul_const _)]
  apply integral_congr_ae
  filter_upwards with y
  change (ρ j y*DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) 0 j)*star (v 1)-
    (ρ j y*DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) 1 j)*star (v 0)=
      ρ j y*(DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) 0 j*star (v 1)-
        DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) 1 j*star (v 0))
  ring

theorem magnetic_cross_columns (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (v : Vector) :
    crossProduct v (conjugate (MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q))) 2 =
      ∑ j : Fin 3, ∫ y, conj (ρ j y)*crossProduct v
        (conjugate (fun i => magneticDyadic k (MaxwellPlaneTail.planePoint q-y) i j)) 2 := by
  change v 0*star (MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) 1)-
    v 1*star (MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q) 0)=_
  rw [← magnetic_column_sum k R d hd ρ hρ q 1, ← magnetic_column_sum k R d hd ρ hρ q 0]
  simp only [star_sum, Complex.star_def]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_conj, ← integral_conj, ← integral_const_mul, ← integral_const_mul,
    ← integral_sub ((conjugate_integrable (magnetic_integrable k R d hd ρ hρ q 1 j)).const_mul _)
      ((conjugate_integrable (magnetic_integrable k R d hd ρ hρ q 0 j)).const_mul _)]
  apply integral_congr_ae
  filter_upwards with y
  change v 0*conj (ρ j y*magneticDyadic k (MaxwellPlaneTail.planePoint q-y) 1 j)-
    v 1*conj (ρ j y*magneticDyadic k (MaxwellPlaneTail.planePoint q-y) 0 j)=_
  simp [cross_apply, conjugate, map_mul]
  ring

theorem electric_cross_integrable (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (v : Vector) (j : Fin 3) :
    Integrable (fun y => ρ j y*crossProduct
      (fun i => DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) i j) (conjugate v) 2) := by
  apply (((electric_integrable k R d hd ρ hρ q 0 j).mul_const (star (v 1))).sub
    ((electric_integrable k R d hd ρ hρ q 1 j).mul_const (star (v 0)))).congr
  filter_upwards with y
  simp only [Pi.sub_apply]
  change ρ j y*DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) 0 j*star (v 1)-
    ρ j y*DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) 1 j*star (v 0)=
      ρ j y*(DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) 0 j*star (v 1)-
        DyadicKernel.dyadic k (MaxwellPlaneTail.planePoint q-y) 1 j*star (v 0))
  ring

theorem magnetic_cross_integrable (k R d : ℝ) (hd : 0 < d) (ρ : Source)
    (hρ : Admissible R d ρ) (q : Plane) (v : Vector) (j : Fin 3) :
    Integrable (fun y => conj (ρ j y)*crossProduct v
      (conjugate (fun i => magneticDyadic k (MaxwellPlaneTail.planePoint q-y) i j)) 2) := by
  apply (((conjugate_integrable (magnetic_integrable k R d hd ρ hρ q 1 j)).const_mul (v 0)).sub
    ((conjugate_integrable (magnetic_integrable k R d hd ρ hρ q 0 j)).const_mul (v 1))).congr
  filter_upwards with y
  simp only [Pi.sub_apply]
  change v 0*conj (ρ j y*magneticDyadic k (MaxwellPlaneTail.planePoint q-y) 1 j)-
    v 1*conj (ρ j y*magneticDyadic k (MaxwellPlaneTail.planePoint q-y) 0 j)=_
  simp [cross_apply, conjugate, map_mul]
  ring
end OQ14.PointSourceColumns
#print axioms OQ14.PointSourceColumns.electric_integrable
#print axioms OQ14.PointSourceColumns.magnetic_integrable
#print axioms OQ14.PointSourceColumns.magnetic_column_sum
#print axioms OQ14.PointSourceColumns.electric_cross_columns
#print axioms OQ14.PointSourceColumns.magnetic_cross_columns

#print axioms OQ14.PointSourceColumns.electric_cross_integrable
#print axioms OQ14.PointSourceColumns.magnetic_cross_integrable
