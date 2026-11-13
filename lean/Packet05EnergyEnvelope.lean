import Packet05ScalarDirectionalUniformQuotients
import Packet05RegionalDirectionalUniform

/-! Monotone scalar envelopes for the actual PDE quotient estimates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05EnergyEnvelope
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.Packet05ScalarDirectionalUniformQuotients

def envelope (P Q d b M a ηa ηb : ℝ) : ℝ :=
  let K := 2+4*M^2
  let Ac := 3*(1+d)*a
  let Bc := 3*ηb
  let Dc := ηa*(9*(1+d)*b*P + Q)
  3*K^2*(2*Ac*Bc*P+Dc)^2 + 2*K*(Dc^2+(Bc*P)^2)

theorem directional_energy_le_envelope (C J : Fin 3 → L2Scalar)
    (P Q d b M a ηa ηb : ℝ)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hηa : 0 ≤ ηa) (hηb : 0 ≤ ηb)
    (hP : ‖C 0‖ + ‖C 1‖ + ‖C 2‖ ≤ P) (hQ : (∑ j : Fin 3, ‖J j‖) ≤ Q) :
    uniformEnergyBound C J d b M a ηa ηb ≤ envelope P Q d b M a ηa ηb := by
  have hP0 : 0 ≤ P := (by positivity : 0 ≤ ‖C 0‖ + ‖C 1‖ + ‖C 2‖).trans hP
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun _ _ => norm_nonneg _) : 0 ≤ ∑ j : Fin 3, ‖J j‖) |>.trans hQ
  let P' := ‖C 0‖ + ‖C 1‖ + ‖C 2‖
  let Q' := ∑ j : Fin 3, ‖J j‖
  let K := 2+4*M^2
  let A := 3*(1+d)*a
  let B := 3*ηb
  let D := ηa*(9*(1+d)*b*P+Q)
  let D' := ηa*(9*(1+d)*b*P'+Q')
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hP' : 0 ≤ P' := by dsimp [P']; positivity
  have hQ' : 0 ≤ Q' := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hD' : 0 ≤ D' := by dsimp [D']; positivity
  have hD : D' ≤ D := by
    dsimp [D,D',P',Q']
    gcongr
  have hAP : A*B*P' ≤ A*B*P := by gcongr
  have hBP : B*P' ≤ B*P := by gcongr
  have hsum : 2*A*B*P'+D' ≤ 2*A*B*P+D := by nlinarith
  have hsum0 : 0 ≤ 2*A*B*P'+D' := by positivity
  have hDsq := pow_le_pow_left₀ hD' hD 2
  have hBsq := pow_le_pow_left₀ (mul_nonneg hB hP') hBP 2
  have hSsq := pow_le_pow_left₀ hsum0 hsum 2
  change 3*K^2*(2*A*B*P'+D')^2 + 2*K*(D'^2+(B*P')^2) ≤
    3*K^2*(2*A*B*P+D)^2 + 2*K*(D^2+(B*P)^2)
  gcongr


theorem regional_energy_le_envelope (C J : Fin 3 → L2Scalar)
    (P Q d b M a ηa ηb : ℝ)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hηa : 0 ≤ ηa) (hηb : 0 ≤ ηb)
    (hP : ‖C 0‖ + ‖C 1‖ + ‖C 2‖ ≤ P) (hQ : (∑ j : Fin 3, ‖J j‖) ≤ Q) :
    OQ14.Packet05RegionalDirectionalUniform.uniformEnergyBound C J d b M a ηa ηb ≤
      envelope P Q d b M a ηa ηb :=
  directional_energy_le_envelope C J P Q d b M a ηa ηb hd hb ha hηa hηb hP hQ

theorem derivative_bound_le_envelope (C J : Fin 3 → L2Scalar) (v : L2Scalar) (j : Fin 3)
    (P Q d b M a ηa ηb : ℝ)
    (hd : 0 ≤ d) (hb : 0 ≤ b) (ha : 0 ≤ a) (hηa : 0 ≤ ηa) (hηb : 0 ≤ ηb)
    (hP : ‖C 0‖ + ‖C 1‖ + ‖C 2‖ ≤ P) (hQ : (∑ j : Fin 3, ‖J j‖) ≤ Q)
    (hv : ‖v‖ ≤ Real.sqrt (uniformEnergyBound C J d b M a ηa ηb) + 3*ηb*‖C j‖) :
    ‖v‖ ≤ Real.sqrt (envelope P Q d b M a ηa ηb) + 3*ηb*P := by
  have henergy := directional_energy_le_envelope C J P Q d b M a ηa ηb hd hb ha hηa hηb hP hQ
  have hcoord : ‖C j‖ ≤ P := by
    have hs := Finset.single_le_sum (f := fun i : Fin 3 => ‖C i‖) (fun i _ => norm_nonneg (C i)) (Finset.mem_univ j)
    have hs' : ‖C j‖ ≤ ‖C 0‖ + ‖C 1‖ + ‖C 2‖ := by simpa only [Fin.sum_univ_three] using hs
    exact hs'.trans hP
  exact hv.trans (add_le_add (Real.sqrt_le_sqrt henergy)
    (mul_le_mul_of_nonneg_left hcoord (by positivity)))

end OQ14.Packet05EnergyEnvelope
#print axioms OQ14.Packet05EnergyEnvelope.directional_energy_le_envelope

#print axioms OQ14.Packet05EnergyEnvelope.regional_energy_le_envelope
#print axioms OQ14.Packet05EnergyEnvelope.derivative_bound_le_envelope
