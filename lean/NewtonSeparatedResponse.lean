import StaticPlaneInclusions
import NewtonExteriorResponse

/-! Genuine Newton spatial representatives on a source-free strip about the plane. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.NewtonSeparatedResponse

open MeasureTheory Metric Set StaticPlaneKernel
open scoped Topology SchwartzMap

def strip (d : ℝ) : Set Space := {x | |x 2| < d/2}

theorem strip_open (d : ℝ) : IsOpen (strip d) :=
  isOpen_lt ((EuclideanSpace.proj 2).continuous.abs) continuous_const

theorem separation (d : ℝ) (x y : Space) (hx : x ∈ strip d) (hy : d ≤ |y 2|) :
    d/2 ≤ ‖x-y‖ := by
  have hi : |x 2-y 2| ≤ ‖x-y‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) 2
  have ha := abs_sub_abs_le_abs_sub (y 2) (x 2)
  rw [abs_sub_comm] at ha
  change |x 2| < d/2 at hx
  linarith

theorem weakConvolution_pairing (ρ : Space → ℂ) (hρ : Integrable ρ) (d : ℝ) (hd : 0 < d)
    (S : ℝ) (hc : ∀ y, y ∉ closedBall 0 S → ρ y=0)
    (hh : ∀ y, ρ y ≠ 0 → d ≤ |y 2|) (i j : Fin 3)
    (f : DynamicSource.Test) (hf : tsupport (f.val : Space → ℂ) ⊆ strip d) :
    NewtonConvolution.weakConvolution ρ i j f.val =
      ∫ x, KernelConvolution.response (NewtonExteriorResponse.awayKernel (d/2) i j) ρ x*f.val x := by
  rw [KernelConvolution.response_pairing _ _
    (NewtonExteriorResponse.awayKernel_locallyIntegrable (d/2) (by positivity) i j)
    hρ (NewtonExteriorResponse.source_compact ρ S hc) f]
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards with y
  by_cases hz : ρ y=0
  · simp only [hz, zero_mul]
  have hy := hh y hz
  have hfy : y ∉ tsupport (f.val : Space → ℂ) := by
    intro hmem
    have hsmall := hf hmem
    change |y 2| < d/2 at hsmall
    linarith
  rw [FieldResponse.weakHessian_symmetric i j, NewtonExterior.translated_weakHessian_away i j f y hfy]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : f.val x=0
  · simp only [hx, mul_zero]
  have hs := separation d x y (hf (subset_tsupport _ hx)) hy
  simp [NewtonExteriorResponse.awayKernel, hs]

theorem newton_pairing (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (d S : ℝ) (hd : 0 < d) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (i : Fin 3)
    (f : DynamicSource.Test) (hf : tsupport (f.val : Space → ℂ) ⊆ strip d) :
    (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x*f.val x) =
      ∫ x, NewtonExteriorResponse.cutResponse (d/2) ρ x i*f.val x := by
  rw [NewtonL1L2.newtonOperator_spatial_pairing F (fun j => (hρ j).congr (hF j).symm)]
  simp only [NewtonExteriorResponse.cutResponse, Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ =>
    FieldResponse.response_test_integrable _ (ρ j)
      (NewtonExteriorResponse.awayKernel_locallyIntegrable (d/2) (by positivity) i j)
      (hρ j) (NewtonExteriorResponse.source_compact _ S (hc j)) f)]
  apply Finset.sum_congr rfl
  intro j _
  rw [← weakConvolution_pairing (ρ j) (hρ j) d hd S (hc j) (hh j) i j f hf]
  unfold NewtonConvolution.weakConvolution
  apply integral_congr_ae
  filter_upwards [hF j] with y hy
  rw [hy]

theorem newton_ae_cutResponse (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (d S : ℝ) (hd : 0 < d) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ strip d →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x =
        NewtonExteriorResponse.cutResponse (d/2) ρ x i := by
  have hN := (Lp.memLp (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i)).locallyIntegrable
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hC := NewtonExteriorResponse.cutResponse_locallyIntegrable F ρ hρ hF (d/2) S
    (by positivity) hc i
  have hz := (strip_open d).ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun x => NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x-
      NewtonExteriorResponse.cutResponse (d/2) ρ x i) ((hN.sub hC).locallyIntegrableOn _)
  have ht : ∀ (g : Space → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ strip d →
      (∫ x, g x • (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x-
        NewtonExteriorResponse.cutResponse (d/2) ρ x i))=0 := by
    intro g hg hgc hgu
    have hgc' : HasCompactSupport (fun x => (g x : ℂ)) :=
      hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    let f : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz
      (fun x => (g x : ℂ)) (Complex.ofRealCLM.contDiff.comp hg) hgc', hgc'⟩
    have hs : tsupport (f.val : Space → ℂ)=tsupport g := by
      change closure (Function.support (fun x => (g x : ℂ)))=closure (Function.support g)
      ext x
      simp [Function.support]
    have hp := newton_pairing F ρ hρ hF d S hd hc hh i f (hs ▸ hgu)
    have hn := NewtonL2.scalar_pairing_integrable
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i) f.val
    have hct := NewtonExteriorResponse.cutResponse_test_integrable ρ hρ (d/2) S
      (by positivity) hc i f
    have he : (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x*f.val x-
        NewtonExteriorResponse.cutResponse (d/2) ρ x i*f.val x)=0 := by
      rw [integral_sub hn hct, hp, sub_self]
    convert he using 1
    apply integral_congr_ae
    filter_upwards with x
    change (g x : ℂ)*(_-_) = _*(g x : ℂ)-_*(g x : ℂ)
    ring
  filter_upwards [hz ht] with x hx hstrip
  exact sub_eq_zero.mp (hx hstrip)

def response (ρ : Fin 3 → Space → ℂ) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j, KernelConvolution.response (fun z => GreenKernel.phiHessian 0 z i j) (ρ j) x

theorem cutResponse_eq (ρ : Fin 3 → Space → ℂ) (d : ℝ)
    (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (x : Space) (hx : x ∈ strip d) (i : Fin 3) :
    NewtonExteriorResponse.cutResponse (d/2) ρ x i=response ρ x i := by
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  by_cases hz : ρ j y=0
  · simp [KernelConvolution.response, hz]
  have hs := separation d x y hx (hh j y hz)
  simp [NewtonExteriorResponse.awayKernel, hs]

theorem newton_ae_response (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (d S : ℝ) (hd : 0 < d) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ strip d →
      NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x=response ρ x i := by
  filter_upwards [newton_ae_cutResponse F ρ hρ hF d S hd hc hh i] with x hx hstrip
  exact (hx hstrip).trans (cutResponse_eq ρ d hh x hstrip i)

theorem kernel_bound (d : ℝ) (hd : 0 < d) (x : Space) (hx : x ∈ strip d)
    (y : Space) (hy : d ≤ |y 2|) (i j : Fin 3) :
    ‖GreenKernel.phiHessian 0 (x-y) i j‖ ≤ (1/Real.pi)*(d/2)⁻¹^3 := by
  have hs := separation d x y hx hy
  have hd2 : 0 < d/2 := by positivity
  have hn : x-y ≠ 0 := norm_pos_iff.mp (hd2.trans_le hs)
  apply (static_hessian_bound (x-y) hn i j).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
    (inv_le_inv₀ (hd2.trans_le hs) hd2 |>.mpr hs) 3

theorem scalar_integrand_integrable (ρ : Space → ℂ) (hρ : Integrable ρ)
    (d : ℝ) (hd : 0 < d) (hh : ∀ y, ρ y ≠ 0 → d ≤ |y 2|)
    (x : Space) (hx : x ∈ strip d) (i j : Fin 3) :
    Integrable (fun y => ρ y*GreenKernel.phiHessian 0 (x-y) i j) := by
  apply (hρ.norm.mul_const ((1/Real.pi)*(d/2)⁻¹^3)).mono'
    (hρ.aestronglyMeasurable.mul ((hessian_measurable i j).comp
      (continuous_const.sub continuous_id).measurable).aestronglyMeasurable)
  filter_upwards with y
  change ‖ρ y*GreenKernel.phiHessian 0 (x-y) i j‖ ≤ _
  by_cases hz : ρ y=0
  · simp [hz]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (kernel_bound d hd x hx y (hh y hz) i j) (norm_nonneg _)

theorem scalar_response_continuousAt (ρ : Space → ℂ) (hρ : Integrable ρ)
    (d : ℝ) (hd : 0 < d) (hh : ∀ y, ρ y ≠ 0 → d ≤ |y 2|)
    (x : Space) (hx : x ∈ strip d) (i j : Fin 3) :
    ContinuousAt (KernelConvolution.response (fun z => GreenKernel.phiHessian 0 z i j) ρ) x := by
  apply continuousAt_of_dominated (F := fun z y => ρ y*GreenKernel.phiHessian 0 (z-y) i j)
    (bound := fun y => ‖ρ y‖*((1/Real.pi)*(d/2)⁻¹^3))
  · filter_upwards [(strip_open d).mem_nhds hx] with z hz
    exact (scalar_integrand_integrable ρ hρ d hd hh z hz i j).aestronglyMeasurable
  · filter_upwards [(strip_open d).mem_nhds hx] with z hz
    filter_upwards with y
    by_cases hy : ρ y=0
    · simp [hy]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (kernel_bound d hd z hz y (hh y hy) i j) (norm_nonneg _)
  · exact hρ.norm.mul_const _
  · filter_upwards with y
    by_cases hy : ρ y=0
    · simp only [hy, zero_mul]
      exact continuousAt_const
    have hn : x-y ≠ 0 := norm_pos_iff.mp
      ((by positivity : 0 < d/2).trans_le (separation d x y hx (hh y hy)))
    exact continuousAt_const.mul ((NewtonExterior.hessian_continuousAt 0 i j (x-y) hn).comp
      (f := fun z : Space => z-y) (continuous_id.sub continuous_const).continuousAt)

theorem response_continuousOn (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (d : ℝ) (hd : 0 < d) (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (i : Fin 3) :
    ContinuousOn (fun x => response ρ x i) (strip d) := by
  intro x hx
  have ht : ContinuousAt (fun z => response ρ z i) x :=
    tendsto_finset_sum _ (fun j _ =>
      scalar_response_continuousAt (ρ j) (hρ j) d hd (hh j) x hx i j)
  exact ht.continuousWithinAt

theorem response_plane (ρ : Fin 3 → Space → ℂ) (q : PlaneInverseCube.Plane) (i : Fin 3) :
    response ρ (MaxwellPlaneTail.planePoint q) i =
      ∑ j, StaticPlaneSource.field (ρ j) i j q := by
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  exact mul_comm _ _

theorem continuous_representative (F : VectorFourier.VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j))
    (hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] ρ j)
    (d S : ℝ) (hd : 0 < d) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y=0)
    (hh : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|) (i : Fin 3) :
    ∃ g : Space → ℂ, ContinuousOn g (strip d) ∧
      (∀ᵐ x : Space, x ∈ strip d → NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x=g x) ∧
      ∀ q : PlaneInverseCube.Plane, g (MaxwellPlaneTail.planePoint q)=
        ∑ j, StaticPlaneSource.field (ρ j) i j q :=
  ⟨fun x => response ρ x i, response_continuousOn ρ hρ d hd hh i,
    newton_ae_response F ρ hρ hF d S hd hc hh i, fun q => response_plane ρ q i⟩

theorem representative_unique (d : ℝ) (g h : Space → ℂ)
    (hg : ContinuousOn g (strip d)) (hh : ContinuousOn h (strip d))
    (he : ∀ᵐ x : Space, x ∈ strip d → g x=h x) : EqOn g h (strip d) := by
  exact Measure.eqOn_open_of_ae_eq (μ := (volume : Measure Space))
    ((ae_restrict_iff' (strip_open d).measurableSet).mpr he)
    (strip_open d) hg hh

end OQ14.NewtonSeparatedResponse

#print axioms OQ14.NewtonSeparatedResponse.strip_open
#print axioms OQ14.NewtonSeparatedResponse.separation
#print axioms OQ14.NewtonSeparatedResponse.weakConvolution_pairing
#print axioms OQ14.NewtonSeparatedResponse.newton_pairing
#print axioms OQ14.NewtonSeparatedResponse.newton_ae_cutResponse
#print axioms OQ14.NewtonSeparatedResponse.cutResponse_eq
#print axioms OQ14.NewtonSeparatedResponse.newton_ae_response
#print axioms OQ14.NewtonSeparatedResponse.kernel_bound
#print axioms OQ14.NewtonSeparatedResponse.scalar_integrand_integrable
#print axioms OQ14.NewtonSeparatedResponse.scalar_response_continuousAt
#print axioms OQ14.NewtonSeparatedResponse.response_continuousOn
#print axioms OQ14.NewtonSeparatedResponse.response_plane
#print axioms OQ14.NewtonSeparatedResponse.continuous_representative
#print axioms OQ14.NewtonSeparatedResponse.representative_unique
