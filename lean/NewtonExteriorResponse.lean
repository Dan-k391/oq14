import NewtonExterior
import LocalConvolution

/-! # Actual Newton response on regions separated from the source

An ordinary Hessian kernel with its central ball removed is locally integrable.
Exterior tests remove that cutoff exactly, so the previously established
spatial weak Hessian identifies the actual L2 response there.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.NewtonExteriorResponse

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel
open scoped SchwartzMap

def awayKernel (δ : ℝ) (i j : Fin 3) (x : Space) : ℂ :=
  {z : Space | δ ≤ ‖z‖}.indicator (fun z => phiHessian 0 z i j) x

theorem awayKernel_locallyIntegrable (δ : ℝ) (hδ : 0 < δ) (i j : Fin 3) :
    LocallyIntegrable (awayKernel δ i j) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hs : IsClosed {z : Space | δ ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  have ha := hK.inter_right hs
  have hh : ContinuousOn (fun z => phiHessian 0 z i j) (K ∩ {z : Space | δ ≤ ‖z‖}) := by
    intro x hx
    exact (NewtonExterior.hessian_continuousAt 0 i j x
      (by intro he; subst x; exact hδ.not_le (by simpa using hx.2))).continuousWithinAt
  have hi : IntegrableOn (fun z => phiHessian 0 z i j)
      (K ∩ {z : Space | δ ≤ ‖z‖}) volume := hh.integrableOn_compact ha
  change Integrable ({z : Space | δ ≤ ‖z‖}.indicator
    (fun z => phiHessian 0 z i j)) (volume.restrict K)
  apply (integrable_indicator_iff hs.measurableSet).mpr
  simpa only [IntegrableOn, Measure.restrict_restrict hs.measurableSet, Set.inter_comm] using hi

theorem source_compact (ρ : Space → ℂ) (S : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) : HasCompactSupport ρ :=
  HasCompactSupport.intro' (isCompact_closedBall 0 S) isClosed_closedBall hc

theorem separation (δ R S : ℝ) (hgap : δ+S ≤ R) (x y : Space)
    (hx : R < ‖x‖) (hy : y ∈ closedBall 0 S) : δ ≤ ‖x-y‖ := by
  have hn := norm_add_le (x-y) y
  rw [sub_add_cancel] at hn
  simp only [mem_closedBall, dist_zero_right] at hy
  linarith

theorem awayKernel_source_eq (ρ : Space → ℂ) (δ R S : ℝ) (hgap : δ+S ≤ R)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (i j : Fin 3) (x y : Space)
    (hx : R < ‖x‖) :
    ρ y * awayKernel δ i j (x-y) = ρ y * phiHessian 0 (x-y) i j := by
  by_cases hy : y ∈ closedBall (0 : Space) S
  · simp [awayKernel, separation δ R S hgap x y hx hy]
  · simp only [hc y hy, zero_mul]

theorem weakConvolution_exterior_pairing (ρ : Space → ℂ) (hρ : Integrable ρ volume)
    (δ R S : ℝ) (hδ : 0 < δ) (hgap : δ+S ≤ R)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (i j : Fin 3)
    (f : DynamicSource.Test) (hf : tsupport (f.val : Space → ℂ) ⊆ {x | R < ‖x‖}) :
    NewtonConvolution.weakConvolution ρ i j f.val =
      ∫ x, KernelConvolution.response (awayKernel δ i j) ρ x * f.val x := by
  rw [KernelConvolution.response_pairing _ _ (awayKernel_locallyIntegrable δ hδ i j)
    hρ (source_compact ρ S hc) f]
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards with y
  by_cases hz : ρ y = 0
  · simp only [hz, zero_mul]
  have hy : y ∈ closedBall (0 : Space) S := by
    by_contra hn
    exact hz (hc y hn)
  have hfy : y ∉ tsupport (f.val : Space → ℂ) := by
    intro he
    have hny := hf he
    simp only [mem_closedBall, dist_zero_right] at hy
    change R < ‖y‖ at hny
    linarith
  rw [FieldResponse.weakHessian_symmetric i j,
    NewtonExterior.translated_weakHessian_away i j f y hfy]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : f.val x = 0
  · simp only [hx, mul_zero]
  have hs := separation δ R S hgap x y (hf (subset_tsupport _ hx)) hy
  simp [awayKernel, hs]

def cutResponse (δ : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j, KernelConvolution.response (awayKernel δ i j) (ρ j) x

theorem cutResponse_locallyIntegrable (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (δ S : ℝ) (hδ : 0 < δ)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) (i : Fin 3) :
    LocallyIntegrable (fun x => cutResponse δ ρ x i) volume := by
  apply locallyIntegrable_finset_sum
  intro j _
  exact LocalConvolution.response_locallyIntegrable _ (awayKernel_locallyIntegrable δ hδ i j)
    (ρ j) (hρ j) (NewtonL2.physicalCoordinate F j) (hF j) S (hc j)

theorem cutResponse_test_integrable (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j) volume) (δ S : ℝ) (hδ : 0 < δ)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (i : Fin 3) (f : DynamicSource.Test) :
    Integrable (fun x => cutResponse δ ρ x i * f.val x) volume := by
  simp only [cutResponse, Finset.sum_mul]
  exact integrable_finset_sum Finset.univ (fun j _ =>
    FieldResponse.response_test_integrable _ (ρ j) (awayKernel_locallyIntegrable δ hδ i j)
      (hρ j) (source_compact _ S (hc j)) f)

theorem newton_cutResponse_pairing (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (δ R S : ℝ) (hδ : 0 < δ) (hgap : δ+S ≤ R)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (i : Fin 3) (f : DynamicSource.Test)
    (hf : tsupport (f.val : Space → ℂ) ⊆ {x | R < ‖x‖}) :
    (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x * f.val x) =
      ∫ x, cutResponse δ ρ x i * f.val x := by
  rw [NewtonL1L2.newtonOperator_spatial_pairing F (fun j => (hρ j).congr (hF j).symm)]
  simp only [cutResponse, Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ =>
    FieldResponse.response_test_integrable _ (ρ j) (awayKernel_locallyIntegrable δ hδ i j)
      (hρ j) (source_compact _ S (hc j)) f)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← weakConvolution_exterior_pairing (ρ j) (hρ j) δ R S hδ hgap (hc j) i j f hf]
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards [hF j] with y hy
  rw [hy]

theorem newton_ae_cutResponse_exterior (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (δ R S : ℝ) (hδ : 0 < δ) (hgap : δ+S ≤ R)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), R < ‖x‖ →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x = cutResponse δ ρ x i := by
  have hU : IsOpen {x : Space | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hN := (Lp.memLp (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i)).locallyIntegrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hC := cutResponse_locallyIntegrable F ρ hρ hF δ S hδ hc i
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x -
      cutResponse δ ρ x i) ((hN.sub hC).locallyIntegrableOn _)
  have hh : ∀ (g : Space → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ {x : Space | R < ‖x‖} →
      (∫ x, g x • (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x -
        cutResponse δ ρ x i)) = 0 := by
    intro g hg hgc hgU
    have hgc' : HasCompactSupport (fun x => (g x : ℂ)) :=
      hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    let f : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz
      (fun x => (g x : ℂ)) (Complex.ofRealCLM.contDiff.comp hg) hgc', hgc'⟩
    have hs : tsupport (f.val : Space → ℂ) = tsupport g := by
      change closure (Function.support (fun x => (g x : ℂ))) = closure (Function.support g)
      ext x
      simp [Function.support]
    have hp := newton_cutResponse_pairing F ρ hρ hF δ R S hδ hgap hc i f (hs ▸ hgU)
    have hn := NewtonL2.scalar_pairing_integrable
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i) f.val
    have hd := cutResponse_test_integrable ρ hρ δ S hδ hc i f
    have he : (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x * f.val x -
        cutResponse δ ρ x i * f.val x) = 0 := by
      rw [integral_sub hn hd, hp, sub_self]
    convert he using 1
    apply integral_congr_ae
    filter_upwards with x
    change (g x : ℂ) * (_ - _) = _ * (g x : ℂ) - _ * (g x : ℂ)
    ring
  filter_upwards [hz hh] with x hx hRx
  exact sub_eq_zero.mp (hx hRx)

theorem cutResponse_eq_exterior (ρ : Fin 3 → Space → ℂ) (δ R S : ℝ) (hgap : δ+S ≤ R)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) (i : Fin 3) (x : Space)
    (hx : R < ‖x‖) :
    cutResponse δ ρ x i = ∑ j, ∫ y, ρ j y * phiHessian 0 (x-y) i j := by
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  exact awayKernel_source_eq (ρ j) δ R S hgap (hc j) i j x y hx

/-- The actual bounded Newton operator agrees with the ordinary spatial
Hessian integral almost everywhere outside every larger source ball. -/
theorem newton_ae_exterior (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (R S : ℝ) (hRS : S < R)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), R < ‖x‖ →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x =
        ∑ j, ∫ y, ρ j y * phiHessian 0 (x-y) i j := by
  have hd : 0 < (R-S)/2 := by linarith
  have hg : (R-S)/2+S ≤ R := by linarith
  filter_upwards [newton_ae_cutResponse_exterior F ρ hρ hF ((R-S)/2) R S hd hg hc i]
    with x hx hRx
  exact (hx hRx).trans (cutResponse_eq_exterior ρ _ R S hg hc i x hRx)

theorem source_integrand_integrable (q ρ : Space → ℂ)
    (hq : ∀ z, z ≠ 0 → ContinuousAt q z) (hρ : Integrable ρ volume) (S : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (x : Space) (hx : S < ‖x‖) :
    Integrable (fun y => ρ y * q (x-y)) volume := by
  have hqK : ContinuousOn (fun y => q (x-y)) (closedBall 0 S) := by
    intro y hy
    have hn : x-y ≠ 0 := by
      intro he
      have hxy := sub_eq_zero.mp he
      subst y
      exact (not_le_of_gt hx) (by simpa only [mem_closedBall, dist_zero_right] using hy)
    exact ((hq (x-y) hn).comp (continuous_const.sub continuous_id).continuousAt).continuousWithinAt
  have hi : IntegrableOn (fun y => ρ y * q (x-y)) (closedBall 0 S) volume :=
    hρ.integrableOn.mul_continuousOn hqK (isCompact_closedBall 0 S)
  have he : (closedBall 0 S).indicator (fun y => ρ y * q (x-y)) =
      (fun y => ρ y * q (x-y)) := by
    apply Set.indicator_eq_self.mpr
    intro y hy
    by_contra hn
    exact hy (by simp [hc y hn])
  rw [← he]
  exact (integrable_indicator_iff measurableSet_closedBall).mpr hi

theorem remainder_continuousAt (k : ℝ) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (fun y => DyadicKernel.remainder k y i j) x := by
  unfold DyadicKernel.remainder DyadicKernel.dyadic
  exact (((continuousAt_const.mul (phi_contDiffAt k x hx).continuousAt).mul continuousAt_const).add
    (NewtonExterior.hessian_continuousAt k i j x hx)).sub
      (NewtonExterior.hessian_continuousAt 0 i j x hx)

theorem hessian_source_integrable (ρ : Space → ℂ) (hρ : Integrable ρ volume)
    (S : ℝ) (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0)
    (x : Space) (hx : S < ‖x‖) (i j : Fin 3) :
    Integrable (fun y => ρ y * phiHessian 0 (x-y) i j) volume :=
  source_integrand_integrable _ ρ (NewtonExterior.hessian_continuousAt 0 i j) hρ S hc x hx

/-- The previously constructed electric field is the ordinary outgoing
dyadic source integral almost everywhere on every source-separated exterior. -/
theorem electric_ae_exterior (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (R S : ℝ) (hRS : S < R)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) (i : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), R < ‖x‖ →
      FieldResponse.electric k F ρ x i =
        ∑ j, ∫ y, ρ j y * DyadicKernel.dyadic k (x-y) i j := by
  filter_upwards [newton_ae_exterior F ρ hρ hF R S hRS hc i] with x hx hRx
  simp only [FieldResponse.electric, hx hRx, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hSx := hRS.trans hRx
  rw [KernelConvolution.response, ← integral_add
    (hessian_source_integrable (ρ j) (hρ j) S (hc j) x hSx i j)
    (source_integrand_integrable _ (ρ j) (remainder_continuousAt k i j)
      (hρ j) S (hc j) x hSx)]
  apply integral_congr_ae
  filter_upwards with y
  simp only [DyadicKernel.remainder]
  ring

end OQ14.NewtonExteriorResponse

#print axioms OQ14.NewtonExteriorResponse.awayKernel_locallyIntegrable
#print axioms OQ14.NewtonExteriorResponse.source_compact
#print axioms OQ14.NewtonExteriorResponse.separation
#print axioms OQ14.NewtonExteriorResponse.awayKernel_source_eq
#print axioms OQ14.NewtonExteriorResponse.weakConvolution_exterior_pairing
#print axioms OQ14.NewtonExteriorResponse.cutResponse_locallyIntegrable
#print axioms OQ14.NewtonExteriorResponse.cutResponse_test_integrable
#print axioms OQ14.NewtonExteriorResponse.newton_cutResponse_pairing
#print axioms OQ14.NewtonExteriorResponse.newton_ae_cutResponse_exterior
#print axioms OQ14.NewtonExteriorResponse.cutResponse_eq_exterior
#print axioms OQ14.NewtonExteriorResponse.newton_ae_exterior
#print axioms OQ14.NewtonExteriorResponse.source_integrand_integrable
#print axioms OQ14.NewtonExteriorResponse.remainder_continuousAt
#print axioms OQ14.NewtonExteriorResponse.hessian_source_integrable
#print axioms OQ14.NewtonExteriorResponse.electric_ae_exterior
