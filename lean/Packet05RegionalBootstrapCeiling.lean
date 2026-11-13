import Packet05RegionalBootstrapUniform

/-! Named regional bootstrap ceiling, fixed by chart coefficients and data
ceilings before selecting a member of the family. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05RegionalBootstrapCeiling

def ceiling (P F1b d b M a τa τb α β γ ξ U0 F0 F2b c : ℝ) : ℝ :=
  let H := Real.sqrt (Packet05EnergyEnvelope.envelope P F1b d b M a τa τb) + 3*τb*P
  let K0 := α*U0
  let K1 := α*P+β*U0
  let K2 := α*F0+3*(1+d)*a*β*U0
  let K3 := α*F1b+β*F0+(1+d)*(3*a*(β*P+γ*U0)+3*b*β*U0)
  let K4 := α*F2b + β*(F1b+F1b) + γ*F0 + (1+d)*3*
    (a*(β*H + 2*γ*P + ξ*U0) + 2*b*(β*P+γ*U0) + c*β*U0)
  max 0 (max K0 (max K1 (max K2 (max K3 K4))))

theorem ceiling_nonneg (P F1b d b M a τa τb α β γ ξ U0 F0 F2b c : ℝ) :
    0 ≤ ceiling P F1b d b M a τa τb α β γ ξ U0 F0 F2b c := le_max_left _ _

end OQ14.Packet05RegionalBootstrapCeiling
#print axioms OQ14.Packet05RegionalBootstrapCeiling.ceiling_nonneg
