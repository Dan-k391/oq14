import Packet05SecondEnvelope
import Packet05ScalarDirectionalUniformQuotients

/-! Bound all second-iteration numerical data uniformly by original norms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05SecondEnvelopeOriginal
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.Packet05EnergyEnvelope
  OQ14.Packet05EnergyEnvelopeMonotone OQ14.Packet05SecondEnvelope

theorem actual_first_le (C F : Fin 3 → L2Scalar) (P Q d b M a τa τb : ℝ)
    (hP : (∑ j : Fin 3, ‖C j‖) ≤ P) (hQ : (∑ j : Fin 3, ‖F j‖) ≤ Q)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hτa : 0 ≤ τa) (hτb : 0 ≤ τb) :
    3 * Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound C F d b M a τa τb) +
      3*τb*(∑ j : Fin 3, ‖C j‖) ≤ first P Q d b M a τa τb := by
  have he := directional_energy_le_envelope C F P Q d b M a τa τb hd hb ha hτa hτb
    (by simpa only [Fin.sum_univ_three] using hP) hQ
  have hs := Real.sqrt_le_sqrt he
  have hp := mul_le_mul_of_nonneg_left hP (show 0 ≤ 3*τb by positivity)
  dsimp only [first]
  linarith

theorem actual_second_numerical_le (C F Fi Ft Fit : Fin 3 → L2Scalar)
    (P F0 F1 F2 F12 d b M a c τa τb τc κa κb κc ηa ηb : ℝ)
    (hP : (∑ j : Fin 3, ‖C j‖) ≤ P) (hF0 : (∑ j : Fin 3, ‖F j‖) ≤ F0)
    (hF1 : (∑ j : Fin 3, ‖Fi j‖) ≤ F1) (hF2 : (∑ j : Fin 3, ‖Ft j‖) ≤ F2)
    (hF12 : (∑ j : Fin 3, ‖Fit j‖) ≤ F12)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hτa : 0 ≤ τa) (hτb : 0 ≤ τb) (hτc : 0 ≤ τc)
    (hκa : 0 ≤ κa) (hκb : 0 ≤ κb) (hκc : 0 ≤ κc) (hηa : 0 ≤ ηa) (hηb : 0 ≤ ηb) :
    let P0 := ∑ j : Fin 3, ‖C j‖
    let Li := 3 * Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound C Fi d b M a τa τb) + 3*τb*P0
    let Lt := 3 * Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound C Ft d b M a τa τb) + 3*τb*P0
    let Pg := κa*Li + 3*κb*P0
    let Q := κa*(τa*(∑ j : Fin 3, ‖Fit j‖) + τb*((∑ j : Fin 3, ‖Fi j‖)+(∑ j : Fin 3, ‖Ft j‖)) + τc*(∑ j : Fin 3, ‖F j‖) + 3*(1+d)*(b*Lt + c*τa*P0)) +
      κb*(τa*(∑ j : Fin 3, ‖Fi j‖)+τb*(∑ j : Fin 3, ‖F j‖)+3*(1+d)*b*τa*P0) +
      3*(1+d)*(3*a*(κb*Li+κc*P0)+3*b*κb*P0)
    Real.sqrt (envelope Pg Q d b M a ηa ηb) + 3*ηb*Pg ≤
      Real.sqrt (envelope (OQ14.Packet05SecondEnvelope.gradient P F1 d b M a τa τb κa κb)
        (forcing P F0 F1 F2 F12 d b a c τa τb τc κa κb κc M) d b M a ηa ηb) +
        3*ηb*(OQ14.Packet05SecondEnvelope.gradient P F1 d b M a τa τb κa κb) := by
  dsimp only
  let P0 := ∑ j : Fin 3, ‖C j‖
  let Li := 3 * Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound C Fi d b M a τa τb) + 3*τb*P0
  let Lt := 3 * Real.sqrt (OQ14.Packet05ScalarDirectionalUniformQuotients.uniformEnergyBound C Ft d b M a τa τb) + 3*τb*P0
  let Pg := κa*Li + 3*κb*P0
  let Q := κa*(τa*(∑ j : Fin 3, ‖Fit j‖) + τb*((∑ j : Fin 3, ‖Fi j‖)+(∑ j : Fin 3, ‖Ft j‖)) + τc*(∑ j : Fin 3, ‖F j‖) + 3*(1+d)*(b*Lt + c*τa*P0)) +
      κb*(τa*(∑ j : Fin 3, ‖Fi j‖)+τb*(∑ j : Fin 3, ‖F j‖)+3*(1+d)*b*τa*P0) +
      3*(1+d)*(3*a*(κb*Li+κc*P0)+3*b*κb*P0)
  have hP0 : 0 ≤ P0 := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hLi0 : 0 ≤ Li := by dsimp [Li]; positivity
  have hLt0 : 0 ≤ Lt := by dsimp [Lt]; positivity
  have hPg0 : 0 ≤ Pg := by dsimp [Pg]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hi : Li ≤ first P F1 d b M a τa τb := actual_first_le C Fi P F1 d b M a τa τb hP hF1 hd hb ha hτa hτb
  have ht : Lt ≤ first P F2 d b M a τa τb := actual_first_le C Ft P F2 d b M a τa τb hP hF2 hd hb ha hτa hτb
  have hPg : Pg ≤ OQ14.Packet05SecondEnvelope.gradient P F1 d b M a τa τb κa κb := by
    dsimp only [Pg,OQ14.Packet05SecondEnvelope.gradient]
    exact add_le_add (mul_le_mul_of_nonneg_left hi hκa) (mul_le_mul_of_nonneg_left hP (by positivity))
  have hQ : Q ≤ forcing P F0 F1 F2 F12 d b a c τa τb τc κa κb κc M := by
    dsimp only [Q,forcing]
    gcongr
  have he := envelope_mono Pg Q (OQ14.Packet05SecondEnvelope.gradient P F1 d b M a τa τb κa κb)
    (forcing P F0 F1 F2 F12 d b a c τa τb τc κa κb κc M) d b M a ηa ηb
    hPg0 hQ0 hPg hQ hd hb ha hηa hηb
  exact add_le_add (Real.sqrt_le_sqrt he) (mul_le_mul_of_nonneg_left hPg (by positivity))

end OQ14.Packet05SecondEnvelopeOriginal
#print axioms OQ14.Packet05SecondEnvelopeOriginal.actual_first_le
#print axioms OQ14.Packet05SecondEnvelopeOriginal.actual_second_numerical_le
