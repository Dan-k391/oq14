import L1Convolution
import RealKernelBounds
import KernelEstimates

/-!
# Actual localized dynamic dyadic convolution

Each truncated remainder entry is an actual integrable kernel. Scalar Young
bounds give a bounded vector operator, with an explicit quadratic radius bound.
The finite-dimensional estimate deliberately uses the simple factor nine.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.DynamicConvolution

open MeasureTheory Metric
open scoped InnerProductSpace

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev VectorL2 := VectorFourier.VectorL2

def kernel (k R : ℝ) (i j : Fin 3) : Space → ℂ :=
  (closedBall 0 R).indicator (fun x => DyadicKernel.remainder k x i j)

theorem kernel_integrable (k R : ℝ) (i j : Fin 3) : Integrable (kernel k R i j) :=
  (integrable_indicator_iff measurableSet_closedBall).mpr
    (RealKernelBounds.remainder_integrable_ball k R i j)

def entryMass (k R : ℝ) : ℝ :=
  (14 * k^2 / (4 * Real.pi)) *
    ((3 / 2 : ℝ) * (volume : Measure Space).real (ball 0 1) * R^2)

theorem entryMass_nonnegative (k R : ℝ) : 0 ≤ entryMass k R := by
  unfold entryMass
  positivity

theorem kernel_mass (k R : ℝ) (hR : 0 ≤ R) (i j : Fin 3) :
    L1Convolution.mass (kernel k R i j) ≤ entryMass k R := by
  have he : (fun x => ‖kernel k R i j x‖) =
      (closedBall 0 R).indicator (fun x => ‖DyadicKernel.remainder k x i j‖) := by
    ext x
    by_cases hx : x ∈ closedBall (0 : Space) R <;> simp [kernel, hx]
  rw [L1Convolution.mass, he, integral_indicator measurableSet_closedBall]
  have h := integral_mono_ae
    (RealKernelBounds.remainder_integrable_ball k R i j).norm
    ((KernelIntegrability.inverse_norm_integrable_ball R).const_mul (14 * k^2 / (4 * Real.pi)))
    (Filter.Eventually.of_forall (fun x => RealKernelBounds.remainder_bound_all k x i j))
  rw [integral_const_mul, KernelEstimates.inverse_norm_integral_ball R hR] at h
  exact h

def component (j : Fin 3) : VectorL2 →L[ℂ] ScalarL2 :=
  VectorFourier.scalarCoordinates.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    VectorFourier.coordinate j

def insert (i : Fin 3) : ScalarL2 →L[ℂ] VectorL2 :=
  VectorFourier.insertion i ∘L
    VectorFourier.scalarCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem component_apply (j : Fin 3) (F : VectorL2) :
    component j F = NewtonL2.physicalCoordinate F j := rfl

theorem component_norm (j : Fin 3) (F : VectorL2) : ‖component j F‖ ≤ ‖F‖ := by
  change ‖VectorFourier.scalarCoordinates (VectorFourier.coordinate j F)‖ ≤ ‖F‖
  rw [VectorFourier.scalarCoordinates.norm_map]
  have h : ‖VectorFourier.coordinate j F‖ ≤ 1 * ‖F‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [VectorFourier.coordinate_ae j F] with x hx
    rw [hx, one_mul]
    exact PiLp.norm_apply_le (F x) j
  simpa only [one_mul] using h

theorem insert_norm (i : Fin 3) (F : ScalarL2) : ‖insert i F‖ ≤ ‖F‖ := by
  change ‖VectorFourier.insertion i (VectorFourier.scalarCoordinates.symm F)‖ ≤ ‖F‖
  have h : ‖VectorFourier.insertion i (VectorFourier.scalarCoordinates.symm F)‖ ≤
      1 * ‖VectorFourier.scalarCoordinates.symm F‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(VectorFourier.insertionValue i).coeFn_compLpL
      (VectorFourier.scalarCoordinates.symm F)] with x hx
    change VectorFourier.insertion i (VectorFourier.scalarCoordinates.symm F) x =
      VectorFourier.insertionValue i (VectorFourier.scalarCoordinates.symm F x) at hx
    rw [hx]
    simp [VectorFourier.insertionValue, norm_smul, EuclideanSpace.norm_single]
  simpa only [one_mul, VectorFourier.scalarCoordinates.symm.norm_map] using h

theorem component_insert (i j : Fin 3) (F : ScalarL2) :
    component i (insert j F) = if i = j then F else 0 := by
  change VectorFourier.scalarCoordinates
    (VectorFourier.coordinate i (VectorFourier.insertion j
      (VectorFourier.scalarCoordinates.symm F))) = _
  rw [VectorFourier.coordinate_insertion]
  split_ifs <;> simp

def row (k R : ℝ) (i : Fin 3) : VectorL2 →L[ℂ] ScalarL2 :=
  ∑ j : Fin 3, L1Convolution.operator (kernel k R i j) (kernel_integrable k R i j) ∘L component j

def operator (k R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  ∑ i : Fin 3, insert i ∘L row k R i

theorem row_norm (k R : ℝ) (hR : 0 ≤ R) (i : Fin 3) (F : VectorL2) :
    ‖row k R i F‖ ≤ 3 * entryMass k R * ‖F‖ := by
  change ‖∑ j : Fin 3, L1Convolution.operator (kernel k R i j)
    (kernel_integrable k R i j) (component j F)‖ ≤ _
  apply (norm_sum_le _ _).trans
  have h (j : Fin 3) : ‖L1Convolution.operator (kernel k R i j)
      (kernel_integrable k R i j) (component j F)‖ ≤ entryMass k R * ‖F‖ := by
    exact (L1Convolution.operator_norm _ _ _).trans
      (mul_le_mul (kernel_mass k R hR i j) (component_norm j F)
        (norm_nonneg _) (entryMass_nonnegative k R))
  calc
    _ ≤ ∑ _j : Fin 3, entryMass k R * ‖F‖ := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp; ring

theorem operator_norm (k R : ℝ) (hR : 0 ≤ R) (F : VectorL2) :
    ‖operator k R F‖ ≤ (9 * entryMass k R) * ‖F‖ := by
  change ‖∑ i : Fin 3, insert i (row k R i F)‖ ≤ _
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin 3, 3 * entryMass k R * ‖F‖ :=
      Finset.sum_le_sum (fun i _ => (insert_norm i _).trans (row_norm k R hR i F))
    _ = _ := by simp; ring

theorem operator_norm_le (k R : ℝ) (hR : 0 ≤ R) :
    ‖operator k R‖ ≤ 9 * entryMass k R :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (by norm_num) (entryMass_nonnegative k R)) (operator_norm k R hR)

theorem component_operator (k R : ℝ) (F : VectorL2) (i : Fin 3) :
    component i (operator k R F) = row k R i F := by
  change component i (∑ j : Fin 3, insert j (row k R j F)) = _
  simp only [map_sum, component_insert]
  simp

theorem scalar_sum_ae (F : Fin 3 → ScalarL2) :
    (fun x => (∑ j : Fin 3, F j) x) =ᵐ[volume] fun x => ∑ j : Fin 3, F j x := by
  simp only [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (F 0 + F 1) (F 2), Lp.coeFn_add (F 0) (F 1)] with x hx hy
  rw [hx]
  simp only [Pi.add_apply, hy]

theorem operator_ae_convolution (k R : ℝ) (F : VectorL2)
    (hF : ∀ j, Integrable (component j F : Space → ℂ)) (i : Fin 3) :
    (fun x => operator k R F (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => ∑ j : Fin 3, HeatFourier.convolution (kernel k R i j) (component j F) x := by
  have hcoord := (NewtonL2.physicalCoordinate_ae (operator k R F) i).symm
  change (fun x => operator k R F (VectorFourier.coordinateMap x) i) =ᵐ[volume]
    (component i (operator k R F) : Space → ℂ) at hcoord
  rw [component_operator] at hcoord
  apply hcoord.trans
  have hs := scalar_sum_ae (fun j => L1Convolution.operator (kernel k R i j)
    (kernel_integrable k R i j) (component j F))
  have hc := ae_all_iff.mpr (fun j => L1Convolution.operator_ae_convolution
    (kernel k R i j) (kernel_integrable k R i j) (component j F) (hF j))
  filter_upwards [hs, hc] with x hx hy
  change (∑ j : Fin 3, L1Convolution.operator (kernel k R i j)
    (kernel_integrable k R i j) (component j F)) x = _
  rw [hx]
  simp only [hy]

end OQ14.DynamicConvolution

#print axioms OQ14.DynamicConvolution.kernel_integrable
#print axioms OQ14.DynamicConvolution.entryMass_nonnegative
#print axioms OQ14.DynamicConvolution.kernel_mass
#print axioms OQ14.DynamicConvolution.component_apply
#print axioms OQ14.DynamicConvolution.component_norm
#print axioms OQ14.DynamicConvolution.insert_norm
#print axioms OQ14.DynamicConvolution.component_insert
#print axioms OQ14.DynamicConvolution.row_norm
#print axioms OQ14.DynamicConvolution.operator_norm
#print axioms OQ14.DynamicConvolution.operator_norm_le
#print axioms OQ14.DynamicConvolution.component_operator
#print axioms OQ14.DynamicConvolution.scalar_sum_ae
#print axioms OQ14.DynamicConvolution.operator_ae_convolution
