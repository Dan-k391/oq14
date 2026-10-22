import StaticSphereMaterial
import Mathlib.Analysis.Calculus.MeanValue

/-! # Actual incident variation and weighted sphere forcing bounds -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticSphereForcing

open MeasureTheory Metric Set StaticBallNewton StaticSphereMaterial
open scoped Topology BigOperators

theorem ballL2_norm (R : ℝ) :
    ‖StaticBallSymbol.ballL2 R‖ = Real.sqrt (volume.real (ball (0 : Space) R)) := by
  exact DynamicSupportVolume.supportIndicator_norm (ball (0 : Space) R) measurableSet_ball
    measure_ball_lt_top.ne

theorem source_norm_le (c : Space) (R : ℝ) (P : Vector) :
    ‖StaticBallCentered.source c R P‖ ≤
      (∑ i : Fin 3, ‖P i‖) * Real.sqrt (volume.real (ball (0 : Space) R)) := by
  apply (DynamicSupportVolume.vector_norm_le_sum_components (StaticBallCentered.source c R P)).trans_eq
  simp only [DynamicConvolution.component_apply, StaticBallCentered.source,
    physicalCoordinate_fromComponents, norm_smul, (StaticBallTranslation.scalar c).norm_map,
    ballL2_norm, Finset.sum_mul]

theorem forcing_error_bound (c : Space) (R χ : ℝ) (hχ : 0 ≤ χ)
    (f : VectorL2) (incident : Maxwell.Field) (E : Vector) (M : ℝ)
    (hincident : ∀ i : Fin 3, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((coefficient c R χ hχ).value (VectorFourier.coordinateMap x)) : ℂ) *
        incident x i)
    (hvariation : ∀ x ∈ ball c R, ∀ i : Fin 3, ‖incident x i-E i‖ ≤ M) :
    ‖f-forcing c R χ E‖ ≤
      (3*Real.sqrt χ*M)*Real.sqrt (volume.real (ball (0 : Space) R)) := by
  have hi : ∀ i : Fin 3, ‖DynamicConvolution.component i (f-forcing c R χ E)‖ ≤
      (Real.sqrt χ*M)*Real.sqrt (volume.real (ball (0 : Space) R)) := by
    intro i
    have hp := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (Lp.coeFn_sub f (forcing c R χ E))
    have hb : ∀ᵐ x : Space,
        ‖DynamicConvolution.component i (f-forcing c R χ E) x‖ ≤
          (Real.sqrt χ*M)*‖StaticBallTranslation.scalar c (StaticBallSymbol.ballL2 R) x‖ := by
      filter_upwards [NewtonL2.physicalCoordinate_ae (f-forcing c R χ E) i, hp, hincident i,
        StaticBallCentered.source_ae c R ((Real.sqrt χ : ℂ) • E) i,
        StaticBallTranslation.translated_ball_ae c R] with x hc hp hf he hb
      rw [DynamicConvolution.component_apply, hc, hp, Pi.sub_apply, PiLp.sub_apply, hf]
      change ‖(Real.sqrt ((coefficient c R χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
        incident x i - forcing c R χ E (VectorFourier.coordinateMap x) i‖ ≤ _
      rw [show forcing c R χ E (VectorFourier.coordinateMap x) i =
        (ball c R).indicator (fun _ => ((Real.sqrt χ : ℂ) • E) i) x from he,
        hb, coefficient_value]
      by_cases hm : x ∈ ball c R
      · rw [if_pos hm, indicator_of_mem hm, indicator_of_mem hm]
        change ‖(Real.sqrt χ : ℂ)*incident x i-(Real.sqrt χ : ℂ)*E i‖ ≤ (Real.sqrt χ*M)*‖(1 : ℂ)‖
        rw [← mul_sub, norm_mul, norm_one, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (Real.sqrt_nonneg χ)]
        exact mul_le_mul_of_nonneg_left (hvariation x hm i) (Real.sqrt_nonneg _)
      · simp [hm]
    have hn := Lp.norm_le_mul_norm_of_ae_le_mul hb
    rwa [(StaticBallTranslation.scalar c).norm_map, ballL2_norm] at hn
  calc
    _ ≤ ∑ i : Fin 3, ‖DynamicConvolution.component i (f-forcing c R χ E)‖ :=
      DynamicSupportVolume.vector_norm_le_sum_components _
    _ ≤ ∑ _i : Fin 3, (Real.sqrt χ*M)*Real.sqrt (volume.real (ball (0 : Space) R)) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by simp only [Fin.sum_univ_three]; ring

theorem incident_variation_of_derivative (c : Space) (R : ℝ) (hR : 0 < R)
    (incident : Maxwell.Field) (L : ℝ) (hL : 0 ≤ L)
    (hdiff : ∀ i : Fin 3, ∀ x ∈ ball c R, DifferentiableAt ℝ (fun y => incident y i) x)
    (hder : ∀ i : Fin 3, ∀ x ∈ ball c R, ‖fderiv ℝ (fun y => incident y i) x‖ ≤ L)
    (x : Space) (hx : x ∈ ball c R) (i : Fin 3) :
    ‖incident x i-incident c i‖ ≤ L*R := by
  have hc : c ∈ ball c R := by simpa only [mem_ball, dist_self] using hR
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le (hdiff i) (hder i) (convex_ball c R) hc hx
  exact he.trans (mul_le_mul_of_nonneg_left
    (by exact (show ‖x-c‖ < R by simpa only [mem_ball, dist_eq_norm] using hx).le) hL)

end OQ14.StaticSphereForcing

#print axioms OQ14.StaticSphereForcing.ballL2_norm
#print axioms OQ14.StaticSphereForcing.source_norm_le
#print axioms OQ14.StaticSphereForcing.forcing_error_bound
#print axioms OQ14.StaticSphereForcing.incident_variation_of_derivative
