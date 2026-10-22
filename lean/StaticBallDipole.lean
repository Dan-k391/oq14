import FiniteSphereAsymptotics

/-! # Actual constant-ball source moments and exact exterior dipole fields -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.StaticBallDipole

open MeasureTheory Metric Set StaticBallNewton
open scoped Topology BigOperators

theorem indicator_integrable (c : Space) (R : ℝ) (z : ℂ) :
    Integrable ((ball c R).indicator (fun _ => z)) :=
  (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_const.mpr (Or.inr measure_ball_lt_top))

theorem source_integrable (c : Space) (R : ℝ) (P : Vector) (i : Fin 3) :
    Integrable (fun x => StaticBallCentered.source c R P (VectorFourier.coordinateMap x) i) :=
  (indicator_integrable c R (P i)).congr (StaticBallCentered.source_ae c R P i).symm

theorem source_moment (c : Space) (R : ℝ) (P : Vector) (i : Fin 3) :
    (∫ x, StaticBallCentered.source c R P (VectorFourier.coordinateMap x) i) =
      (volume.real (ball c R) : ℂ)*P i := by
  rw [integral_congr_ae (StaticBallCentered.source_ae c R P i), integral_indicator_const _ measurableSet_ball]
  rfl

theorem exterior_eq_volume_kernel (c : Space) (R : ℝ) (hR : 0 ≤ R) (x : Space) (hx : x ≠ 0)
    (i j : Fin 3) :
    StaticBallHessian.exterior R ‖x‖ i j x =
      (volume.real (ball c R) : ℂ)*GreenKernel.phiHessian 0 x i j := by
  have hv : volume.real (ball c R) = R^3*(Real.pi*4/3) := by
    simp only [measureReal_def, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]
  have hn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hx
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hv]
  unfold StaticBallHessian.exterior GreenKernel.phiHessian GreenKernel.radialDD GreenKernel.radialD
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0),
    Complex.exp_zero, one_mul, zero_div, zero_sub, zero_add]
  push_cast
  ring_nf
  field_simp [hn, hp]
  split_ifs <;> ring

theorem newton_source_dipole (c : Space) (R : ℝ) (hR : 0 < R) (P : Vector) (i : Fin 3) :
    ∀ᵐ x : Space, R < ‖x-c‖ →
      NewtonL2.newtonOperator (StaticBallCentered.source c R P) (VectorFourier.coordinateMap x) i =
        ∑ j : Fin 3, GreenKernel.phiHessian 0 (x-c) i j * ((volume.real (ball c R) : ℂ)*P j) := by
  rw [StaticBallCentered.newton_source c R hR P]
  filter_upwards [StaticBallCentered.response_ae c R hR P i] with x hx hout
  have hn : x-c ≠ 0 := norm_ne_zero_iff.mp (hR.trans hout).ne'
  rw [hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [StaticBallHessian.hessian, if_neg (not_le.mpr hout), exterior_eq_volume_kernel c R hR.le (x-c) hn]
  ring

theorem finite_source_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (m : Fin 3) :
    (∫ x, FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap x) m) =
      ∑ j : ι, (volume.real (ball (p j) (r j)) : ℂ)*P j m := by
  rw [integral_congr_ae (FiniteSphereStatic.sumSource_ae p r P m),
    integral_finset_sum _ (fun j _ => indicator_integrable (p j) (r j) (P j m))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator_const _ measurableSet_ball]
  rfl

end OQ14.StaticBallDipole

#print axioms OQ14.StaticBallDipole.indicator_integrable
#print axioms OQ14.StaticBallDipole.source_integrable
#print axioms OQ14.StaticBallDipole.source_moment
#print axioms OQ14.StaticBallDipole.exterior_eq_volume_kernel
#print axioms OQ14.StaticBallDipole.newton_source_dipole
#print axioms OQ14.StaticBallDipole.finite_source_moment
