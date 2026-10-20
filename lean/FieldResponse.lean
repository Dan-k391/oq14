import WaveResponse
import NewtonL1L2

/-! # Actual spatial electric response and its distributional Maxwell equation -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.FieldResponse

open MeasureTheory OQ14.Maxwell OQ14.DynamicSource
open scoped SchwartzMap

theorem response_test_integrable (q ρ : Space → ℂ) (hq : LocallyIntegrable q)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : Test) :
    Integrable (fun x => KernelConvolution.response q ρ x * f.val x) := by
  apply (KernelConvolution.product_integrable q ρ hq hρ hc f).integral_prod_left.congr
  filter_upwards with x
  rw [KernelConvolution.response, integral_mul_const]

theorem weakHessian_symmetric (i j : Fin 3) (f : 𝓢(Space, ℂ)) :
    NewtonHessian.weakHessian i j f = NewtonHessian.weakHessian j i f := by
  unfold NewtonHessian.weakHessian
  apply integral_congr_ae
  filter_upwards with x
  change GreenKernel.phi 0 x * dcoord (fun y => dcoord f y j) x i =
    GreenKernel.phi 0 x * dcoord (fun y => dcoord f y i) x j
  rw [Maxwell.partial_comm (f.smooth 2)]

def electric (k : ℝ) (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ) : Field :=
  fun x i => NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x +
    ∑ j, KernelConvolution.response (fun z => DyadicKernel.remainder k z i j) (ρ j) x

theorem electric_test_integrable (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j, HasCompactSupport (ρ j)) (i : Fin 3) (f : Test) :
    Integrable (fun x => electric k F ρ x i * f.val x) := by
  have hs := NewtonL2.scalar_pairing_integrable
    (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i) f.val
  have hd (j : Fin 3) := response_test_integrable
    (fun z => DyadicKernel.remainder k z i j) (ρ j)
    (RealKernelBounds.remainder_locallyIntegrable k i j) (hρ j) (hc j) f
  simpa only [electric, add_mul, Finset.sum_mul] using
    hs.add (integrable_finset_sum Finset.univ (fun j _ => hd j))

/-- The concrete field has the full dyadic convolution action; the static
part is the constructed L2 Newton response and the dynamic part is a literal
spatial integral. -/
theorem electric_pairing (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) (f : Test) :
    (∫ x, electric k F ρ x i * f.val x) =
      ∑ j, WaveResponse.columnPair k (ρ j) i j f := by
  have hs := NewtonL2.scalar_pairing_integrable
    (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i) f.val
  have hd (j : Fin 3) := response_test_integrable
    (fun z => DyadicKernel.remainder k z i j) (ρ j)
    (RealKernelBounds.remainder_locallyIntegrable k i j) (hρ j) (hc j) f
  simp only [electric, add_mul, Finset.sum_mul]
  rw [integral_add hs (integrable_finset_sum Finset.univ (fun j _ => hd j)),
    integral_finset_sum _ (fun j _ => hd j),
    NewtonL1L2.newtonOperator_spatial_pairing F
      (fun j => (hρ j).congr (hF j).symm), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [WaveResponse.column_decomposition k (ρ j) (hρ j) (hc j)]
  congr 1
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards [hF j] with y hy
  rw [hy, weakHessian_symmetric i j]

/-- Actual inhomogeneous Maxwell curl-curl equation for every compact smooth
scalar test and every coordinate of the constructed spatial field. -/
theorem electric_maxwell_source (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) (f : Test) :
    (∑ l : Fin 3, ∫ x, electric k F ρ x l *
      (testPartial l (testPartial i f)).val x) -
      (∑ l : Fin 3, ∫ x, electric k F ρ x i *
        (testPartial l (testPartial l f)).val x) -
        (k : ℂ)^2 * (∫ x, electric k F ρ x i * f.val x) =
          (k : ℂ)^2 * (∫ x, ρ i x * f.val x) := by
  simp_rw [electric_pairing k F ρ hρ hc hF]
  have ha : (∑ l : Fin 3, ∑ j : Fin 3,
      WaveResponse.columnPair k (ρ j) l j (testPartial l (testPartial i f))) =
      ∑ j : Fin 3, ∑ l : Fin 3,
        WaveResponse.columnPair k (ρ j) l j (testPartial l (testPartial i f)) :=
    Finset.sum_comm
  have hb : (∑ l : Fin 3, ∑ j : Fin 3,
      WaveResponse.columnPair k (ρ j) i j (testPartial l (testPartial l f))) =
      ∑ j : Fin 3, ∑ l : Fin 3,
        WaveResponse.columnPair k (ρ j) i j (testPartial l (testPartial l f)) :=
    Finset.sum_comm
  rw [ha, hb, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  simp_rw [WaveResponse.column_maxwell_source k _ (hρ _) (hc _)]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

end OQ14.FieldResponse

#print axioms OQ14.FieldResponse.response_test_integrable
#print axioms OQ14.FieldResponse.weakHessian_symmetric
#print axioms OQ14.FieldResponse.electric_test_integrable
#print axioms OQ14.FieldResponse.electric_pairing
#print axioms OQ14.FieldResponse.electric_maxwell_source
