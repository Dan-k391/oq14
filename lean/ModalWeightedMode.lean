import ModalPoleMode
import StaticSphereMaterial
import IncidentLocalization
import MaterialVolumeConverse
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Actual compactly supported weighted electric modes of the dielectric sphere.
The field used here is the global residue mode, including its regular center.
This constructs the vector and proves its nontriviality; identification with
the complex-frequency volume kernel is a separate representation step. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalWeightedMode

open MeasureTheory Metric Set Complex OQ14.Maxwell OQ14.ModalMatching
  OQ14.ModalAlgebra OQ14.ModalShell OQ14.ModalPoleMode OQ14.ModalOrigin
open scoped Topology

theorem contrast_pos (n : ℝ) (hn : 1 < n) : 0 < n ^ 2 - 1 := by nlinarith

def coefficient (n : ℝ) (hn : 1 < n) : StaticCoefficient.Coefficient :=
  StaticSphereMaterial.coefficient 0 1 (n ^ 2 - 1) (contrast_pos n hn).le

theorem coefficient_value (n : ℝ) (hn : 1 < n) (x : Space) :
    (coefficient n hn).value (VectorFourier.coordinateMap x) =
      if ‖x‖ < 1 then n ^ 2 - 1 else 0 := by
  simp only [coefficient, StaticSphereMaterial.coefficient_value, mem_ball, dist_zero_right]

theorem coefficient_support (n : ℝ) (hn : 1 < n) (x : Space)
    (hx : x ∉ closedBall (0 : Space) 1) :
    (coefficient n hn).value (VectorFourier.coordinateMap x) = 0 := by
  have h : ¬ ‖x‖ < 1 := by
    intro hlt
    apply hx
    simpa only [mem_closedBall, dist_zero_right] using hlt.le
  rw [coefficient_value, if_neg h]

theorem coefficient_agrees_ae (n : ℝ) (hn : 1 < n) :
    (fun x : Space => (1 : ℂ) + (coefficient n hn).value (VectorFourier.coordinateMap x))
      =ᵐ[volume] ModalProfiles.coefficient (n : ℂ) := by
  filter_upwards [OQ14.RadialInterface.ae_regular 1] with x hx
  rw [coefficient_value]
  by_cases hi : ‖x‖ < 1
  · simp only [if_pos hi, ModalProfiles.coefficient, if_pos hi.le]
    push_cast
    ring
  · have ho : ¬ ‖x‖ ≤ 1 := fun h => hi (lt_of_le_of_ne h hx.2)
    simp [hi, ModalProfiles.coefficient, ho]

def weightedMode (n : ℝ) (hn : 1 < n) (k : Frequency) (f : Amplitudes) :
    VectorFourier.VectorL2 :=
  IncidentLocalization.datum (coefficient n hn) 1 (electricMode (n : ℂ) k.1 f)
    (coefficient_support n hn)
    (fun i => (residue_local_L2 (n : ℂ) k.1 k.property f
      (closedBall (0 : Space) 1) isBounded_closedBall i).1)

theorem weightedMode_actual (n : ℝ) (hn : 1 < n) (k : Frequency) (f : Amplitudes)
    (i : Fin 3) :
    (fun x => weightedMode n hn k f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
        electricMode (n : ℂ) k.1 f x i :=
  IncidentLocalization.datum_actual _ _ _ _ _ i

theorem weightedMode_source (n : ℝ) (hn : 1 < n) (k : Frequency) (f : Amplitudes)
    (i : Fin 3) :
    DynamicVolume.source (coefficient n hn) (weightedMode n hn k f) i =ᵐ[volume]
      fun x => ((coefficient n hn).value (VectorFourier.coordinateMap x) : ℂ) *
        electricMode (n : ℂ) k.1 f x i :=
  MaterialVolumeConverse.source_from_weighted _ _ _ (weightedMode_actual n hn k f) i

theorem weightedMode_inner (n : ℝ) (hn : 1 < n) (k : Frequency) (f : Amplitudes)
    (i : Fin 3) :
    (fun x => weightedMode n hn k f (VectorFourier.coordinateMap x) i)
      =ᵐ[volume.restrict (ball (0 : Space) 1)]
      fun x => (Real.sqrt (n ^ 2 - 1) : ℂ) *
        entireInnerE (n : ℂ) k.1 (residue 1 (n : ℂ) k.1 f).1 x i := by
  filter_upwards [ae_restrict_of_ae (weightedMode_actual n hn k f i),
    ae_restrict_mem measurableSet_ball] with x hx hi
  have hi' : ‖x‖ < 1 := by simpa using hi
  rw [hx, coefficient_value, if_pos hi']
  simp only [electricMode, ModalProfiles.electric, if_pos hi'.le]

theorem weightedMode_ne_zero (n : ℝ) (hn : 1 < n) (k : Frequency) (f : Amplitudes)
    (ha : (residue 1 (n : ℂ) k.1 f).1 ≠ 0) : weightedMode n hn k f ≠ 0 := by
  intro hzero
  have he := weightedMode_inner n hn k f 2
  have haez : (fun x : Space => (Real.sqrt (n ^ 2 - 1) : ℂ) *
      entireInnerE (n : ℂ) k.1 (residue 1 (n : ℂ) k.1 f).1 x 2)
      =ᵐ[volume.restrict (ball (0 : Space) 1)] fun _ => (0 : ℂ) := by
    have hz := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (Lp.coeFn_zero VectorFourier.Vector 2 (volume : Measure VectorFourier.Frequency))
    filter_upwards [he, ae_restrict_of_ae hz] with x hx hz
    rw [hzero] at hx
    rw [hz] at hx
    simpa only [PiLp.zero_apply] using hx.symm
  have hc : Continuous (fun x : Space => (Real.sqrt (n ^ 2 - 1) : ℂ) *
      entireInnerE (n : ℂ) k.1 (residue 1 (n : ℂ) k.1 f).1 x 2) :=
    continuous_const.mul (continuous_const.mul (centerE_continuous ((n : ℂ) * k.1) 2))
  have heq := Measure.eqOn_open_of_ae_eq haez isOpen_ball hc.continuousOn
    continuous_const.continuousOn
  have hz := heq (show (0 : Space) ∈ ball (0 : Space) 1 by simp)
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hs : (Real.sqrt (n ^ 2 - 1) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (contrast_pos n hn)))
  have hv : (Real.sqrt (n ^ 2 - 1) : ℂ) *
      ((residue 1 (n : ℂ) k.1 f).1 / n * (2 * ((n : ℂ) * k.1) ^ 2 / 3)) ≠ 0 :=
    mul_ne_zero hs (mul_ne_zero (div_ne_zero ha hn0)
      (div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (mul_ne_zero hn0 k.property)))
        (by norm_num)))
  apply hv
  simpa only [entireInnerE, Pi.smul_apply, smul_eq_mul, centerE_zero,
    Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero] using hz

theorem exists_nonzero_weighted_residue (n : ℝ) (hn : 1 < n) (k : Frequency)
    (hd : tmDet 1 (n : ℂ) k.1 = 0) (hs : deriv (tmDet 1 (n : ℂ)) k.1 ≠ 0) :
    ∃ f : Amplitudes, weightedMode n hn k f ≠ 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  obtain ⟨f, ha, _, _⟩ := residue_nontrivial (n : ℂ) k hn0 hd hs
  exact ⟨f, weightedMode_ne_zero n hn k f ha⟩

end OQ14.ModalWeightedMode

#print axioms OQ14.ModalWeightedMode.contrast_pos
#print axioms OQ14.ModalWeightedMode.coefficient_value
#print axioms OQ14.ModalWeightedMode.coefficient_support
#print axioms OQ14.ModalWeightedMode.coefficient_agrees_ae
#print axioms OQ14.ModalWeightedMode.weightedMode_actual
#print axioms OQ14.ModalWeightedMode.weightedMode_source
#print axioms OQ14.ModalWeightedMode.weightedMode_inner
#print axioms OQ14.ModalWeightedMode.weightedMode_ne_zero
#print axioms OQ14.ModalWeightedMode.exists_nonzero_weighted_residue
