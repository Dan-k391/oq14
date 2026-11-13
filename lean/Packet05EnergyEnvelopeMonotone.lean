import Packet05EnergyEnvelope

/-! Monotonicity of the explicit chart energy envelope. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05EnergyEnvelopeMonotone
open OQ14.Packet05EnergyEnvelope

theorem envelope_mono (P Q P' Q' d b M a ηa ηb : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hPP : P ≤ P') (hQQ : Q ≤ Q')
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hηa : 0 ≤ ηa) (hηb : 0 ≤ ηb) :
    envelope P Q d b M a ηa ηb ≤ envelope P' Q' d b M a ηa ηb := by
  let K := 2+4*M^2
  let A := 3*(1+d)*a
  let B := 3*ηb
  let D := ηa*(9*(1+d)*b*P+Q)
  let D' := ηa*(9*(1+d)*b*P'+Q')
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hD : D ≤ D' := by dsimp [D,D']; gcongr
  have hAP : A*B*P ≤ A*B*P' := by gcongr
  have hBP : B*P ≤ B*P' := by gcongr
  have hsum : 2*A*B*P+D ≤ 2*A*B*P'+D' := by nlinarith
  have hsum0 : 0 ≤ 2*A*B*P+D := by positivity
  have hDsq := pow_le_pow_left₀ hD0 hD 2
  have hBsq := pow_le_pow_left₀ (mul_nonneg hB hP) hBP 2
  have hSsq := pow_le_pow_left₀ hsum0 hsum 2
  change 3*K^2*(2*A*B*P+D)^2 + 2*K*(D^2+(B*P)^2) ≤
    3*K^2*(2*A*B*P'+D')^2 + 2*K*(D'^2+(B*P')^2)
  gcongr

end OQ14.Packet05EnergyEnvelopeMonotone
#print axioms OQ14.Packet05EnergyEnvelopeMonotone.envelope_mono
