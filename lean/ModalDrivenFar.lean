import ModalDrivenScattering
import RadiatingTrace

noncomputable section
set_option autoImplicit false
namespace OQ14.ModalDrivenFar
open Complex OQ14.Maxwell OQ14.ModalDriven OQ14.AngularPower OQ14.MaxwellRadiation

def axis : Vector := ![0,0,1]
def amplitude (k : ℝ) (b : ℂ) (n : Sphere) : Vector :=
  fun i => (-I * (k : ℂ) * b) * crossProduct (crossProduct (direction n) axis) (direction n) i

theorem transverse (k : ℝ) (b : ℂ) (n : Sphere) : dot (direction n) (amplitude k b n) = 0 := by
  simp [dot, amplitude, cross_apply, axis]
  ring

theorem scaled_outerA (k r : ℝ) (b : ℂ) (hk : k ≠ 0) (hr : r ≠ 0) :
    MaxwellFarField.factor k r * ModalProfiles.outerA (k : ℂ) b r =
      -b*(k : ℂ)*(I - 1/((k : ℂ)*r) - I/((k : ℂ)*r)^2) := by
  have hk' : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hex : exp (-I * (k : ℂ) * (r : ℂ)) * exp (I * ((k : ℂ) * r)) = 1 := by
    rw [← exp_add]
    convert exp_zero using 1; ring
  calc
    _ = (-b*(k : ℂ)*(I - 1/((k : ℂ)*r) - I/((k : ℂ)*r)^2)) *
        (exp (-I * (k : ℂ) * r) * exp (I * ((k : ℂ) * r))) := by
      unfold MaxwellFarField.factor ModalProfiles.outerA ModalAlgebra.xiD
      rw [ModalAlgebra.p_one, ModalAlgebra.pD_one]
      norm_num
      field_simp [hk', hr']
      ring_nf
      simp [I_sq, sub_eq_add_neg]
    _ = _ := by rw [hex, mul_one]
theorem scaled_outerC (k r : ℝ) (b : ℂ) (hk : k ≠ 0) (hr : r ≠ 0) :
    MaxwellFarField.factor k r * (r : ℂ) * ModalProfiles.outerC (k : ℂ) b r =
      -b*I*(k : ℂ)*(1+I/((k : ℂ)*r)) := by
  have hk' : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hex : exp (-I * (k : ℂ) * (r : ℂ)) * exp (I * ((k : ℂ) * r)) = 1 := by
    rw [← exp_add]; convert exp_zero using 1; ring
  calc
    _ = (-b*I*(k : ℂ)*(1+I/((k : ℂ)*r))) *
        (exp (-I * (k : ℂ) * r) * exp (I * ((k : ℂ) * r))) := by
      unfold MaxwellFarField.factor ModalProfiles.outerC ModalAlgebra.xi
      rw [ModalAlgebra.p_one]
      norm_num
      field_simp [hk', hr']
      ring
    _ = _ := by rw [hex, mul_one]

#print axioms OQ14.ModalDrivenFar.scaled_outerC
#print axioms OQ14.ModalDrivenFar.scaled_outerA
#print axioms OQ14.ModalDrivenFar.transverse
end OQ14.ModalDrivenFar









