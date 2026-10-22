import StaticBallTranslation
import StaticSpherePolarization

/-! # Exact constant-ball Newton response at arbitrary actual centers -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallCentered

open MeasureTheory Metric Set StaticBallNewton
open scoped Topology BigOperators

/-- Actual matrix-symbol identification for genuine L2 component data. -/
theorem newton_from_symbol (B : ScalarL2) (H : Fin 3 → Fin 3 → ScalarL2)
    (hH : ∀ i j, FourierL2.fourierEquiv (H i j) =ᵐ[volume] fun ξ =>
      NewtonHessian.hessianSymbol ξ i j * FourierL2.fourierEquiv B ξ) (P : Vector) :
    NewtonL2.newtonOperator (fromComponents (fun j => P j • B)) =
      fromComponents (fun i => ∑ j : Fin 3, P j • H i j) := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro i
  change VectorFourier.coordinate i _ = VectorFourier.coordinate i _
  apply VectorFourier.scalarCoordinates.injective
  change NewtonL2.physicalCoordinate _ i = NewtonL2.physicalCoordinate _ i
  apply FourierL2.fourierEquiv.injective
  apply Lp.ext
  rw [physicalCoordinate_fromComponents, map_sum]
  simp only [map_smul]
  have hn := newton_fourier_ae (fromComponents (fun j => P j • B)) i
  simp only [physicalCoordinate_fromComponents, map_smul] at hn
  have hb : ∀ᵐ ξ : Space, ∀ j : Fin 3,
      (P j • FourierL2.fourierEquiv B : ScalarL2) ξ = P j * FourierL2.fourierEquiv B ξ :=
    ae_all_iff.mpr (fun j => Lp.coeFn_smul (P j) _)
  have hh : ∀ᵐ ξ : Space, ∀ j : Fin 3,
      (P j • FourierL2.fourierEquiv (H i j) : ScalarL2) ξ =
        NewtonHessian.hessianSymbol ξ i j * (P j * FourierL2.fourierEquiv B ξ) := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_smul (P j) (FourierL2.fourierEquiv (H i j)), hH i j] with ξ hs hh
    rw [hs, Pi.smul_apply, smul_eq_mul, hh]
    ring
  filter_upwards [hn, hb, hh,
    StaticBallSymbol.three_sum_ae (fun j => P j • FourierL2.fourierEquiv (H i j))]
    with ξ hn hb hh hsum
  rw [hn, hsum]
  simp only [hb, hh]

def source (c : Space) (R : ℝ) (P : Vector) : VectorL2 :=
  fromComponents (fun i => P i • StaticBallTranslation.scalar c (StaticBallSymbol.ballL2 R))

def response (c : Space) (R : ℝ) (hR : 0 < R) (P : Vector) : VectorL2 :=
  fromComponents (fun i => ∑ j : Fin 3,
    P j • StaticBallTranslation.scalar c (StaticBallL2.hessianL2 R hR i j))

theorem newton_source (c : Space) (R : ℝ) (hR : 0 < R) (P : Vector) :
    NewtonL2.newtonOperator (source c R P) = response c R hR P :=
  newton_from_symbol _ _ (StaticBallTranslation.translated_hessian_fourier_symbol c R hR) P

theorem source_ae (c : Space) (R : ℝ) (P : Vector) (i : Fin 3) :
    (fun x => source c R P (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      (ball c R).indicator (fun _ => P i) := by
  have hc := NewtonL2.physicalCoordinate_ae (source c R P) i
  change NewtonL2.physicalCoordinate (fromComponents _) i =ᵐ[volume] _ at hc
  rw [physicalCoordinate_fromComponents] at hc
  filter_upwards [hc, Lp.coeFn_smul (P i)
    (StaticBallTranslation.scalar c (StaticBallSymbol.ballL2 R)),
    StaticBallTranslation.translated_ball_ae c R] with x hx hs hb
  rw [← hx, hs, Pi.smul_apply, smul_eq_mul, hb]
  by_cases hm : x ∈ ball c R <;> simp [hm]

theorem response_ae (c : Space) (R : ℝ) (hR : 0 < R) (P : Vector) (i : Fin 3) :
    (fun x => response c R hR P (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => ∑ j : Fin 3, P j * StaticBallHessian.hessian R i j (x-c) := by
  have hc := NewtonL2.physicalCoordinate_ae (response c R hR P) i
  change NewtonL2.physicalCoordinate (fromComponents _) i =ᵐ[volume] _ at hc
  rw [physicalCoordinate_fromComponents] at hc
  have hs : ∀ᵐ x : Space, ∀ j : Fin 3,
      (P j • StaticBallTranslation.scalar c (StaticBallL2.hessianL2 R hR i j) : ScalarL2) x =
        P j * StaticBallHessian.hessian R i j (x-c) := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_smul (P j) (StaticBallTranslation.scalar c (StaticBallL2.hessianL2 R hR i j)),
      StaticBallTranslation.translated_hessian_ae c R hR i j] with x hx hh
    rw [hx, Pi.smul_apply, smul_eq_mul, hh]
  filter_upwards [hc, hs, StaticBallSymbol.three_sum_ae
    (fun j => P j • StaticBallTranslation.scalar c (StaticBallL2.hessianL2 R hR i j))]
    with x hx hs hsum
  rw [← hx, hsum]
  simp only [hs]

theorem newton_source_interior (c : Space) (R : ℝ) (hR : 0 < R) (P : Vector) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball c R →
      NewtonL2.newtonOperator (source c R P) (VectorFourier.coordinateMap x) i = -P i/3 := by
  rw [newton_source c R hR P]
  filter_upwards [response_ae c R hR P i] with x hx hm
  have hn : ‖x-c‖ ≤ R := (by simpa only [mem_ball, dist_eq_norm] using hm : ‖x-c‖ < R).le
  rw [hx]
  simp only [StaticBallHessian.hessian, if_pos hn]
  rw [Finset.sum_eq_single i]
  · simp
    ring
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

theorem exact_static_equation (c : Space) (R : ℝ) (hR : 0 < R) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : Vector) (i : Fin 3) :
    (fun x => source c R (StaticSpherePolarization.polarization χ E)
      (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      (ball c R).indicator (fun x => (χ : ℂ) * (E i + NewtonL2.newtonOperator
        (source c R (StaticSpherePolarization.polarization χ E)) (VectorFourier.coordinateMap x) i)) := by
  filter_upwards [source_ae c R (StaticSpherePolarization.polarization χ E) i,
    newton_source_interior c R hR (StaticSpherePolarization.polarization χ E) i] with x hs hn
  rw [hs]
  by_cases hm : x ∈ ball c R
  · rw [indicator_of_mem hm, indicator_of_mem hm, hn hm]
    simpa only [sub_eq_add_neg, neg_div] using StaticSpherePolarization.polarization_identity χ hχ E i
  · rw [indicator_of_not_mem hm, indicator_of_not_mem hm]

end OQ14.StaticBallCentered

#print axioms OQ14.StaticBallCentered.newton_from_symbol
#print axioms OQ14.StaticBallCentered.newton_source
#print axioms OQ14.StaticBallCentered.source_ae
#print axioms OQ14.StaticBallCentered.response_ae
#print axioms OQ14.StaticBallCentered.newton_source_interior
#print axioms OQ14.StaticBallCentered.exact_static_equation
