import StaticBallSymbol

/-! # Exact Newton action on genuine constant-ball L2 sources -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallNewton

open MeasureTheory Metric Set
open scoped Topology BigOperators

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev Vector := VectorFourier.Vector
abbrev VectorL2 := VectorFourier.VectorL2

def fromComponents (F : Fin 3 → ScalarL2) : VectorL2 :=
  VectorFourier.components.symm ((WithLp.equiv 2 (Fin 3 → VectorFourier.ScalarL2)).symm
    (fun i => VectorFourier.scalarCoordinates.symm (F i)))

theorem physicalCoordinate_fromComponents (F : Fin 3 → ScalarL2) (i : Fin 3) :
    NewtonL2.physicalCoordinate (fromComponents F) i = F i := by
  unfold NewtonL2.physicalCoordinate
  change VectorFourier.scalarCoordinates
    (VectorFourier.components (VectorFourier.components.symm _) i) = F i
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact VectorFourier.scalarCoordinates.apply_symm_apply _

def source (R : ℝ) (P : Vector) : VectorL2 :=
  fromComponents (fun i => P i • StaticBallSymbol.ballL2 R)

def response (R : ℝ) (hR : 0 < R) (P : Vector) : VectorL2 :=
  fromComponents (fun i => ∑ j : Fin 3, P j • StaticBallL2.hessianL2 R hR i j)

theorem source_ae (R : ℝ) (P : Vector) (i : Fin 3) :
    (fun x => source R P (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      (ball (0 : Space) R).indicator (fun _ => P i) := by
  have hc := NewtonL2.physicalCoordinate_ae (source R P) i
  change NewtonL2.physicalCoordinate (fromComponents _) i =ᵐ[volume] _ at hc
  rw [physicalCoordinate_fromComponents] at hc
  filter_upwards [hc, Lp.coeFn_smul (P i) (StaticBallSymbol.ballL2 R),
    StaticBallSymbol.ballL2_ae R] with x hx hs hb
  rw [← hx, hs, Pi.smul_apply, smul_eq_mul, hb]
  by_cases hm : x ∈ ball (0 : Space) R <;> simp [hm]

theorem source_fourier_ae (R : ℝ) (P : Vector) (i : Fin 3) :
    FourierL2.fourierEquiv (NewtonL2.physicalCoordinate (source R P) i) =ᵐ[volume]
      fun ξ => P i * FourierL2.fourierEquiv (StaticBallSymbol.ballL2 R) ξ := by
  change FourierL2.fourierEquiv (NewtonL2.physicalCoordinate (fromComponents _) i) =ᵐ[volume] _
  rw [physicalCoordinate_fromComponents, map_smul]
  exact Lp.coeFn_smul _ _

theorem response_ae (R : ℝ) (hR : 0 < R) (P : Vector) (i : Fin 3) :
    (fun x => response R hR P (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => ∑ j : Fin 3, P j * StaticBallHessian.hessian R i j x := by
  have hc := NewtonL2.physicalCoordinate_ae (response R hR P) i
  change NewtonL2.physicalCoordinate (fromComponents _) i =ᵐ[volume] _ at hc
  rw [physicalCoordinate_fromComponents] at hc
  have hs : ∀ᵐ x : Space, ∀ j : Fin 3,
      (P j • StaticBallL2.hessianL2 R hR i j : ScalarL2) x =
        P j * StaticBallHessian.hessian R i j x := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_smul (P j) (StaticBallL2.hessianL2 R hR i j),
      StaticBallL2.hessianL2_ae R hR i j] with x hx hh
    rw [hx, Pi.smul_apply, smul_eq_mul, hh]
  filter_upwards [hc, hs,
    StaticBallSymbol.three_sum_ae (fun j => P j • StaticBallL2.hessianL2 R hR i j)]
    with x hx hs hsum
  rw [← hx, hsum]
  simp only [hs]

theorem response_fourier_ae (R : ℝ) (hR : 0 < R) (P : Vector) (i : Fin 3) :
    FourierL2.fourierEquiv (NewtonL2.physicalCoordinate (response R hR P) i) =ᵐ[volume]
      fun ξ => ∑ j : Fin 3, NewtonHessian.hessianSymbol ξ i j *
        (P j * FourierL2.fourierEquiv (StaticBallSymbol.ballL2 R) ξ) := by
  change FourierL2.fourierEquiv (NewtonL2.physicalCoordinate (fromComponents _) i) =ᵐ[volume] _
  rw [physicalCoordinate_fromComponents, map_sum]
  simp only [map_smul]
  have hs : ∀ᵐ ξ : Space, ∀ j : Fin 3,
      (P j • FourierL2.fourierEquiv (StaticBallL2.hessianL2 R hR i j) : ScalarL2) ξ =
        NewtonHessian.hessianSymbol ξ i j *
          (P j * FourierL2.fourierEquiv (StaticBallSymbol.ballL2 R) ξ) := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [Lp.coeFn_smul (P j) (FourierL2.fourierEquiv (StaticBallL2.hessianL2 R hR i j)),
      StaticBallSymbol.hessian_fourier_symbol R hR i j] with ξ hx hh
    rw [hx, Pi.smul_apply, smul_eq_mul, hh]
    ring
  filter_upwards [hs, StaticBallSymbol.three_sum_ae
    (fun j => P j • FourierL2.fourierEquiv (StaticBallL2.hessianL2 R hR i j))]
    with ξ hs hsum
  rw [hsum]
  simp only [hs]

theorem newton_fourier_ae (F : VectorL2) (i : Fin 3) :
    FourierL2.fourierEquiv (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i)
      =ᵐ[volume] fun ξ => ∑ j : Fin 3, NewtonHessian.hessianSymbol ξ i j *
        FourierL2.fourierEquiv (NewtonL2.physicalCoordinate F j) ξ := by
  rw [← NewtonL2.physicalCoordinate_fourier]
  have he : VectorFourier.fourier (NewtonL2.newtonOperator F) =
      -VectorFourier.fourier (VectorFourier.physicalProjection F) := by
    change VectorFourier.fourier (-VectorFourier.physicalProjection F) = _
    exact map_neg _ _
  have hp := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (NewtonHessian.physicalProjection_hessianSymbol F i)
  have hn := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_neg (VectorFourier.fourier (VectorFourier.physicalProjection F)))
  have hf : ∀ᵐ ξ : Space, ∀ j : Fin 3,
      FourierL2.fourierEquiv (NewtonL2.physicalCoordinate F j) ξ =
        VectorFourier.fourier F (VectorFourier.coordinateMap ξ) j := by
    apply ae_all_iff.mpr
    intro j
    rw [← NewtonL2.physicalCoordinate_fourier]
    exact NewtonL2.physicalCoordinate_ae _ j
  filter_upwards [NewtonL2.physicalCoordinate_ae
    (VectorFourier.fourier (NewtonL2.newtonOperator F)) i, hp, hn, hf]
    with ξ hx hp hn hf
  rw [hx, he, hn]
  change -VectorFourier.fourier (VectorFourier.physicalProjection F)
      (VectorFourier.coordinateMap ξ) i = _
  rw [hp, neg_neg, MeasurableEquiv.symm_apply_apply]
  simp only [hf]

theorem newton_source (R : ℝ) (hR : 0 < R) (P : Vector) :
    NewtonL2.newtonOperator (source R P) = response R hR P := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro i
  change VectorFourier.coordinate i _ = VectorFourier.coordinate i _
  apply VectorFourier.scalarCoordinates.injective
  change NewtonL2.physicalCoordinate _ i = NewtonL2.physicalCoordinate _ i
  apply FourierL2.fourierEquiv.injective
  apply Lp.ext
  have hs : ∀ᵐ ξ : Space, ∀ j : Fin 3,
      FourierL2.fourierEquiv (NewtonL2.physicalCoordinate (source R P) j) ξ =
        P j * FourierL2.fourierEquiv (StaticBallSymbol.ballL2 R) ξ :=
    ae_all_iff.mpr (fun j => source_fourier_ae R P j)
  filter_upwards [newton_fourier_ae (source R P) i, response_fourier_ae R hR P i, hs]
    with ξ hn hr hs
  rw [hn, hr]
  simp only [hs]

theorem newton_source_interior (R : ℝ) (hR : 0 < R) (P : Vector) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) R →
      NewtonL2.newtonOperator (source R P) (VectorFourier.coordinateMap x) i = -P i/3 := by
  rw [newton_source R hR P]
  filter_upwards [response_ae R hR P i] with x hx hm
  have hn : ‖x‖ ≤ R := (by simpa only [mem_ball, dist_zero_right] using hm : ‖x‖ < R).le
  rw [hx]
  simp only [StaticBallHessian.hessian, if_pos hn]
  rw [Finset.sum_eq_single i]
  · simp
    ring
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

end OQ14.StaticBallNewton

#print axioms OQ14.StaticBallNewton.physicalCoordinate_fromComponents
#print axioms OQ14.StaticBallNewton.source_ae
#print axioms OQ14.StaticBallNewton.source_fourier_ae
#print axioms OQ14.StaticBallNewton.response_ae
#print axioms OQ14.StaticBallNewton.response_fourier_ae
#print axioms OQ14.StaticBallNewton.newton_fourier_ae
#print axioms OQ14.StaticBallNewton.newton_source
#print axioms OQ14.StaticBallNewton.newton_source_interior
