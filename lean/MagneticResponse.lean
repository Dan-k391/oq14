import FieldResponse
import NewtonWeak

/-! # Actual magnetic convolution and both first-order Maxwell source equations -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MagneticResponse

open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution
open OQ14.WeakCurl (next previous)

def potentialPair (k : ℝ) (ρ : Space → ℂ) (f : Test) : ℂ :=
  ∫ y, ρ y * scalarPair k (translate y f)

theorem potential_pairing (k : ℝ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : Test) :
    (∫ x, response (GreenKernel.phi k) ρ x * f.val x) = potentialPair k ρ f := by
  rw [response_pairing _ ρ (KernelIntegrability.phi_locallyIntegrable k) hρ hc f]
  simp only [potentialPair, scalarPair, translated_pairing]

theorem gradient_pairing (k : ℝ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i : Fin 3) (f : Test) :
    (∫ x, response (fun z => GreenKernel.phiGradient k z i) ρ x * f.val x) =
      -potentialPair k ρ (testPartial i f) := by
  rw [response_pairing _ ρ (KernelGradient.gradient_locallyIntegrable k i) hρ hc f]
  unfold potentialPair
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  rw [← translated_pairing (fun z => GreenKernel.phiGradient k z i) y f]
  rw [KernelGradient.phi_weak_partial k i (translate y f).val
    ((translate y f).val.smooth 1) (translate y f).property]
  rw [translate_partial]
  simp only [scalarPair, testPartial, GradientProjection.pderivative_apply, mul_neg]

theorem potential_helmholtz (k : ℝ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : Test) :
    (∑ i : Fin 3, potentialPair k ρ (testPartial i (testPartial i f))) +
      (k : ℂ)^2 * potentialPair k ρ f = -(∫ y, ρ y * f.val y) := by
  have hi (g : Test) : Integrable (fun y => ρ y * scalarPair k (translate y g)) :=
    translated_source_integrable (GreenKernel.phi k) ρ
      (KernelIntegrability.phi_locallyIntegrable k) hρ hc g
  have hsum : Integrable (fun y => ∑ i : Fin 3,
      ρ y * scalarPair k (translate y (testPartial i (testPartial i f)))) :=
    integrable_finset_sum Finset.univ (fun i _ => hi _)
  unfold potentialPair
  rw [← integral_finset_sum _ (fun i _ => hi (testPartial i (testPartial i f))),
    ← integral_const_mul, ← integral_add hsum ((hi f).const_mul ((k : ℂ)^2)),
    ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  have h := scalar_helmholtz k (translate y f)
  have hz : (translate y f).val 0 = f.val y := by
    change f.val (0+y) = _
    rw [zero_add]
  rw [hz] at h
  simp only [translate_partial, ← Finset.mul_sum]
  linear_combination ρ y * h

theorem column_potential (k : ℝ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i j : Fin 3) (f : Test) :
    WaveResponse.columnPair k ρ i j f =
      (k : ℂ)^2 * (if i = j then 1 else 0) * potentialPair k ρ f +
        potentialPair k ρ (testPartial j (testPartial i f)) := by
  have hi (g : Test) : Integrable (fun y => ρ y * scalarPair k (translate y g)) :=
    translated_source_integrable (GreenKernel.phi k) ρ
      (KernelIntegrability.phi_locallyIntegrable k) hρ hc g
  have he : (fun y => ρ y * dyadicPair k i j (translate y f)) =
      fun y => ((k : ℂ)^2 * (if i = j then 1 else 0)) *
        (ρ y * scalarPair k (translate y f)) +
        ρ y * scalarPair k (translate y (testPartial j (testPartial i f))) := by
    funext y
    simp only [dyadicPair, translate_partial]
    ring
  unfold WaveResponse.columnPair
  rw [he, integral_add ((hi f).const_mul ((k : ℂ)^2 * (if i = j then 1 else 0)))
    (hi (testPartial j (testPartial i f))), integral_const_mul]
  rfl

theorem electric_potential_pairing (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) (f : Test) :
    (∫ x, FieldResponse.electric k F ρ x i * f.val x) =
      (k : ℂ)^2 * potentialPair k (ρ i) f +
        ∑ j, potentialPair k (ρ j) (testPartial j (testPartial i f)) := by
  rw [FieldResponse.electric_pairing k F ρ hρ hc hF]
  simp_rw [column_potential k _ (hρ _) (hc _)]
  rw [Finset.sum_add_distrib]
  congr 1
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp

def curlPair (A : Fin 3 → Test → ℂ) (i : Fin 3) (f : Test) : ℂ :=
  A (next i) (testPartial (previous i) f) -
    A (previous i) (testPartial (next i) f)

theorem curlPair_curlPair (A : Fin 3 → Test → ℂ) (i : Fin 3) (f : Test) :
    curlPair (curlPair A) i f =
      (∑ j, A j (testPartial j (testPartial i f))) -
        ∑ j, A i (testPartial j (testPartial j f)) := by
  have h01 := partial_commute (0 : Fin 3) 1 f
  have h02 := partial_commute (0 : Fin 3) 2 f
  have h12 := partial_commute (1 : Fin 3) 2 f
  fin_cases i <;>
    simp [curlPair, next, previous, Fin.sum_univ_three, h01, h02, h12] <;> ring

def magnetic (k : ℝ) (ρ : Fin 3 → Space → ℂ) : Field := fun x i =>
  -(Complex.I * (k : ℂ)) *
    (response (fun z => GreenKernel.phiGradient k z (next i)) (ρ (previous i)) x -
      response (fun z => GreenKernel.phiGradient k z (previous i)) (ρ (next i)) x)

theorem magnetic_test_integrable (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (i : Fin 3) (f : Test) :
    Integrable (fun x => magnetic k ρ x i * f.val x) := by
  have hi (j l : Fin 3) := FieldResponse.response_test_integrable
    (fun z => GreenKernel.phiGradient k z j) (ρ l)
    (KernelGradient.gradient_locallyIntegrable k j) (hρ l) (hc l) f
  convert ((hi (next i) (previous i)).sub (hi (previous i) (next i))).const_mul
    (-(Complex.I * (k : ℂ))) using 1
  funext x
  simp only [magnetic, Pi.sub_apply]
  ring

theorem magnetic_pairing (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j, HasCompactSupport (ρ j))
    (i : Fin 3) (f : Test) :
    (∫ x, magnetic k ρ x i * f.val x) =
      -(Complex.I * (k : ℂ)) * curlPair (fun j => potentialPair k (ρ j)) i f := by
  have hi (j l : Fin 3) := FieldResponse.response_test_integrable
    (fun z => GreenKernel.phiGradient k z j) (ρ l)
    (KernelGradient.gradient_locallyIntegrable k j) (hρ l) (hc l) f
  simp only [magnetic, mul_assoc, sub_mul]
  rw [integral_const_mul, integral_sub (hi (next i) (previous i)) (hi (previous i) (next i)),
    gradient_pairing k _ (hρ _) (hc _), gradient_pairing k _ (hρ _) (hc _)]
  unfold curlPair
  ring

theorem electric_curl_pairing (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) (f : Test) :
    (∫ x, FieldResponse.electric k F ρ x (next i) *
      (testPartial (previous i) f).val x) -
      (∫ x, FieldResponse.electric k F ρ x (previous i) *
        (testPartial (next i) f).val x) =
      Complex.I * (k : ℂ) * (∫ x, magnetic k ρ x i * f.val x) := by
  rw [electric_potential_pairing k F ρ hρ hc hF,
    electric_potential_pairing k F ρ hρ hc hF, magnetic_pairing k ρ hρ hc,
    partial_commute (next i) (previous i) f]
  unfold curlPair
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem magnetic_curl_pairing (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j, HasCompactSupport (ρ j))
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) (f : Test) :
    (∫ x, magnetic k ρ x (next i) * (testPartial (previous i) f).val x) -
      (∫ x, magnetic k ρ x (previous i) * (testPartial (next i) f).val x) =
      -(Complex.I * (k : ℂ)) *
        ((∫ x, FieldResponse.electric k F ρ x i * f.val x) +
          (∫ x, ρ i x * f.val x)) := by
  rw [magnetic_pairing k ρ hρ hc, magnetic_pairing k ρ hρ hc,
    electric_potential_pairing k F ρ hρ hc hF, ← mul_sub]
  change -(Complex.I * (k : ℂ)) * curlPair (curlPair (fun j => potentialPair k (ρ j))) i f = _
  rw [curlPair_curlPair]
  have h := potential_helmholtz k (ρ i) (hρ i) (hc i) f
  linear_combination (Complex.I * (k : ℂ)) * h

end OQ14.MagneticResponse

#print axioms OQ14.MagneticResponse.potential_pairing
#print axioms OQ14.MagneticResponse.gradient_pairing
#print axioms OQ14.MagneticResponse.potential_helmholtz
#print axioms OQ14.MagneticResponse.column_potential
#print axioms OQ14.MagneticResponse.electric_potential_pairing
#print axioms OQ14.MagneticResponse.curlPair_curlPair
#print axioms OQ14.MagneticResponse.magnetic_test_integrable
#print axioms OQ14.MagneticResponse.magnetic_pairing
#print axioms OQ14.MagneticResponse.electric_curl_pairing
#print axioms OQ14.MagneticResponse.magnetic_curl_pairing
