import Packet05EnergyEnvelopeMonotone

/-! Numerical family envelope for both tangential PDE iterations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05SecondEnvelope
open OQ14.Packet05EnergyEnvelope OQ14.Packet05EnergyEnvelopeMonotone

def first (P F d b M a τa τb : ℝ) : ℝ :=
  3 * Real.sqrt (envelope P F d b M a τa τb) + 3*τb*P

def gradient (P F d b M a τa τb κa κb : ℝ) : ℝ :=
  κa*first P F d b M a τa τb + 3*κb*P

def forcing (P F0 Fi Ft Fit d b a c τa τb τc κa κb κc M : ℝ) : ℝ :=
  let Li := first P Fi d b M a τa τb
  let Lt := first P Ft d b M a τa τb
  κa*(τa*Fit + τb*(Fi+Ft) + τc*F0 + 3*(1+d)*(b*Lt+c*τa*P)) +
    κb*(τa*Fi+τb*F0+3*(1+d)*b*τa*P) +
    3*(1+d)*(3*a*(κb*Li+κc*P)+3*b*κb*P)

theorem first_nonneg (P F d b M a τa τb : ℝ) (hP : 0 ≤ P) (hτb : 0 ≤ τb) :
    0 ≤ first P F d b M a τa τb := by unfold first; positivity

theorem first_mono (P F P' F' d b M a τa τb : ℝ)
    (hP : 0 ≤ P) (hF : 0 ≤ F) (hPP : P ≤ P') (hFF : F ≤ F')
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hτa : 0 ≤ τa) (hτb : 0 ≤ τb) :
    first P F d b M a τa τb ≤ first P' F' d b M a τa τb := by
  unfold first
  have h := Real.sqrt_le_sqrt (envelope_mono P F P' F' d b M a τa τb hP hF hPP hFF hd hb ha hτa hτb)
  have h' := mul_le_mul_of_nonneg_left hPP (show 0 ≤ 3*τb by positivity)
  linarith

theorem gradient_mono (P Fi P' Fi' d b M a τa τb κa κb : ℝ)
    (hP : 0 ≤ P) (hFi : 0 ≤ Fi) (hPP : P ≤ P') (hFiFi : Fi ≤ Fi')
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hτa : 0 ≤ τa) (hτb : 0 ≤ τb)
    (hκa : 0 ≤ κa) (hκb : 0 ≤ κb) :
    gradient P Fi d b M a τa τb κa κb ≤ gradient P' Fi' d b M a τa τb κa κb := by
  unfold gradient
  have h := first_mono P Fi P' Fi' d b M a τa τb hP hFi hPP hFiFi hd hb ha hτa hτb
  exact add_le_add (mul_le_mul_of_nonneg_left h hκa)
    (mul_le_mul_of_nonneg_left hPP (by positivity))

theorem forcing_mono (P F0 Fi Ft Fit P' F0' Fi' Ft' Fit' d b a c τa τb τc κa κb κc M : ℝ)
    (hP : 0 ≤ P) (hFi : 0 ≤ Fi) (hFt : 0 ≤ Ft)
    (hPP : P ≤ P') (h00 : F0 ≤ F0') (hii : Fi ≤ Fi') (htt : Ft ≤ Ft') (h12 : Fit ≤ Fit')
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hτa : 0 ≤ τa) (hτb : 0 ≤ τb) (hτc : 0 ≤ τc)
    (hκa : 0 ≤ κa) (hκb : 0 ≤ κb) (hκc : 0 ≤ κc) :
    forcing P F0 Fi Ft Fit d b a c τa τb τc κa κb κc M ≤
      forcing P' F0' Fi' Ft' Fit' d b a c τa τb τc κa κb κc M := by
  have hi := first_mono P Fi P' Fi' d b M a τa τb hP hFi hPP hii hd hb ha hτa hτb
  have ht := first_mono P Ft P' Ft' d b M a τa τb hP hFt hPP htt hd hb ha hτa hτb
  dsimp only [forcing]
  gcongr

end OQ14.Packet05SecondEnvelope
#print axioms OQ14.Packet05SecondEnvelope.first_nonneg
#print axioms OQ14.Packet05SecondEnvelope.first_mono
#print axioms OQ14.Packet05SecondEnvelope.gradient_mono
#print axioms OQ14.Packet05SecondEnvelope.forcing_mono
