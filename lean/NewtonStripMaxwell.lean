import NewtonSeparatedResponse
import ExteriorContinuity

/-! Genuine continuous electric and magnetic Maxwell representatives on a source-free strip. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.NewtonStripMaxwell

open MeasureTheory Metric StaticPlaneKernel NewtonSeparatedResponse
open scoped Topology

def remainderBound (k d : ℝ) : ℝ := (14*k^2/(4*Real.pi))*(d/2)⁻¹
def electricBound (k d : ℝ) : ℝ := (1/Real.pi)*(d/2)⁻¹^3+remainderBound k d
def gradientBound (k d : ℝ) : ℝ := (4*Real.pi)⁻¹*(|k| * (d/2)⁻¹+((d/2)⁻¹)^2)

theorem remainder_bound (k d : ℝ) (hd : 0 < d) (z : Space) (hz : d/2 ≤ ‖z‖) (i j : Fin 3) :
    ‖DyadicKernel.remainder k z i j‖ ≤ remainderBound k d := by
  have hd2 : 0 < d/2 := by positivity
  exact (RealKernelBounds.remainder_bound_all k z i j).trans
    (mul_le_mul_of_nonneg_left (inv_le_inv₀ (hd2.trans_le hz) hd2 |>.mpr hz) (by positivity))

theorem electric_bound (k d : ℝ) (hd : 0 < d) (z : Space) (hz : d/2 ≤ ‖z‖) (i j : Fin 3) :
    ‖DyadicKernel.dyadic k z i j‖ ≤ electricBound k d := by
  have hd2 : 0 < d/2 := by positivity
  have hn : z ≠ 0 := norm_pos_iff.mp (hd2.trans_le hz)
  have hi := inv_le_inv₀ (hd2.trans_le hz) hd2 |>.mpr hz
  have he : DyadicKernel.dyadic k z i j=
      GreenKernel.phiHessian 0 z i j+DyadicKernel.remainder k z i j := by
    unfold DyadicKernel.remainder
    ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    ((static_hessian_bound z hn i j).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg z)) hi 3) (by positivity)))
    (remainder_bound k d hd z hz i j))

theorem gradient_bound (k d : ℝ) (hd : 0 < d) (z : Space) (hz : d/2 ≤ ‖z‖) (i : Fin 3) :
    ‖GreenKernel.phiGradient k z i‖ ≤ gradientBound k d := by
  have hd2 : 0 < d/2 := by positivity
  have hi := inv_le_inv₀ (hd2.trans_le hz) hd2 |>.mpr hz
  exact (KernelGradient.gradient_bound k z i).trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hi (abs_nonneg k))
      (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg z)) hi 2)) (by positivity))

private theorem scalar_continuousAt (K ρ : Space → ℂ) (hKm : Measurable K)
    (hK : ∀ z, z ≠ 0 → ContinuousAt K z) (hρ : Integrable ρ)
    (d : ℝ) (hd : 0 < d) (hh : ∀ y, ρ y ≠ 0 → d ≤ |y 2|)
    (C : ℝ) (hb : ∀ z, d/2 ≤ ‖z‖ → ‖K z‖ ≤ C)
    (x : Space) (hx : x ∈ strip d) : ContinuousAt (KernelConvolution.response K ρ) x := by
  apply continuousAt_of_dominated (F := fun z y => ρ y*K (z-y)) (bound := fun y => ‖ρ y‖*C)
  · filter_upwards [(strip_open d).mem_nhds hx] with z hz
    exact (ScalarRadiation.source_integrand_integrable K ρ hKm hρ z C
      (fun y hy => hb (z-y) (separation d z y hz (hh y hy)))).aestronglyMeasurable
  · filter_upwards [(strip_open d).mem_nhds hx] with z hz
    filter_upwards with y
    by_cases hy : ρ y=0
    · simp [hy]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hb (z-y) (separation d z y hz (hh y hy))) (norm_nonneg _)
  · exact hρ.norm.mul_const C
  · filter_upwards with y
    by_cases hy : ρ y=0
    · simp only [hy, zero_mul]
      exact continuousAt_const
    have hn : x-y ≠ 0 := norm_pos_iff.mp
      ((by positivity : 0 < d/2).trans_le (separation d x y hx (hh y hy)))
    exact continuousAt_const.mul ((hK (x-y) hn).comp
      (f := fun z : Space => z-y) (continuous_id.sub continuous_const).continuousAt)

theorem electric_ae_strip (k : ℝ) (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (d S : ℝ) (hd : 0 < d) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ strip d →
      FieldResponse.electric k F ρ x i=ExteriorContinuity.electric k ρ x i := by
  filter_upwards [newton_ae_response F ρ hρ hF d S hd hc hh i] with x hx hstrip
  unfold FieldResponse.electric ExteriorContinuity.electric
  rw [hx hstrip]
  unfold NewtonSeparatedResponse.response
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hi0 := scalar_integrand_integrable (ρ j) (hρ j) d hd (hh j) x hstrip i j
  have hiR := ScalarRadiation.source_integrand_integrable (fun z => DyadicKernel.remainder k z i j)
    (ρ j) (DynamicIntegrability.remainder_measurable k i j) (hρ j) x (remainderBound k d)
    (fun y hy => remainder_bound k d hd (x-y) (separation d x y hstrip (hh j y hy)) i j)
  unfold KernelConvolution.response
  rw [← integral_add hi0 hiR]
  apply integral_congr_ae
  filter_upwards with y
  unfold DyadicKernel.remainder
  ring

theorem electric_continuousOn (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (d : ℝ) (hd : 0 < d)
    (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (i : Fin 3) :
    ContinuousOn (fun x => ExteriorContinuity.electric k ρ x i) (strip d) := by
  intro x hx
  have ht : ContinuousAt (fun z => ExteriorContinuity.electric k ρ z i) x :=
    tendsto_finset_sum _ (fun j _ => scalar_continuousAt _ (ρ j)
      (PlaneSourceKernel.dyadic_measurable k i j) (fun z hz => ExteriorContinuity.dyadic_continuousAt k i j z hz)
      (hρ j) d hd (hh j) (electricBound k d) (fun z hz => electric_bound k d hd z hz i j) x hx)
  exact ht.continuousWithinAt

theorem magnetic_continuousOn (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (d : ℝ) (hd : 0 < d)
    (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (i : Fin 3) :
    ContinuousOn (fun x => MagneticResponse.magnetic k ρ x i) (strip d) := by
  intro x hx
  have hg (j l : Fin 3) := scalar_continuousAt _ (ρ l) (KernelGradient.gradient_measurable k j)
    (fun z hz => (KernelGradient.gradient_differentiableAt k j z hz).continuousAt)
    (hρ l) d hd (hh l) (gradientBound k d) (fun z hz => gradient_bound k d hd z hz j) x hx
  exact (continuousAt_const.mul ((hg (WeakCurl.next i) (WeakCurl.previous i)).sub
    (hg (WeakCurl.previous i) (WeakCurl.next i)))).continuousWithinAt

end OQ14.NewtonStripMaxwell

#print axioms OQ14.NewtonStripMaxwell.remainder_bound
#print axioms OQ14.NewtonStripMaxwell.electric_bound
#print axioms OQ14.NewtonStripMaxwell.gradient_bound
#print axioms OQ14.NewtonStripMaxwell.electric_ae_strip
#print axioms OQ14.NewtonStripMaxwell.electric_continuousOn
#print axioms OQ14.NewtonStripMaxwell.magnetic_continuousOn
