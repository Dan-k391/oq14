import RegularTEIncoming
import FarFieldPower

/-! Exact sphere Poynting identities using the actual tangential magnetic trace. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereTangentialPower
open Complex Maxwell DebyeRadialTrace

theorem tangent_pair (n : Space) (E H : Vector) :
    dot (position n) (crossProduct E (conjugate H))=
      -dot E (conjugate (crossProduct (position n) H)) := by
  simp [dot,conjugate,cross_apply,position,map_sub,map_mul]
  ring

theorem radial_power (n : Space) (hn : ‖n‖=1) (E H : Vector) :
    FarFieldPower.radialPower n E H= -(dot E (conjugate (crossProduct (position n) H))).re/2 := by
  have hd : MaxwellRadiation.direction n=position n := by ext i; simp [MaxwellRadiation.direction,GreenKernel.unitCoordinate,position,hn]
  rw [FarFieldPower.radialPower,hd,tangent_pair,Complex.neg_re]

theorem phase_normSq (inward : Bool) (r : ℝ) :
    normSq (RegularTEIncoming.phase inward r*(r : ℂ))=r^2 := by
  cases inward <;> simp [RegularTEIncoming.phase,normSq_eq_norm_sq,norm_mul,Complex.norm_exp,sq_abs]

theorem scaled_inward_power (n : Space) (hn : ‖n‖=1) (r : ℝ) (E H : Vector) :
    -r^2*FarFieldPower.radialPower n E H=
      (dot ((RegularTEIncoming.phase true r*(r : ℂ)) • E)
        (conjugate ((RegularTEIncoming.phase true r*(r : ℂ)) • crossProduct (position n) H))).re/2 := by
  have h := radial_power n hn ((RegularTEIncoming.phase true r*(r : ℂ)) • E)
    ((RegularTEIncoming.phase true r*(r : ℂ)) • H)
  rw [FarFieldPower.radialPower_smul,phase_normSq,map_smul] at h
  linear_combination -h

end OQ14.SphereTangentialPower
#print axioms OQ14.SphereTangentialPower.tangent_pair
#print axioms OQ14.SphereTangentialPower.radial_power
#print axioms OQ14.SphereTangentialPower.phase_normSq
#print axioms OQ14.SphereTangentialPower.scaled_inward_power
