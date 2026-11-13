import ModalDrivenFar
noncomputable section
set_option autoImplicit false
namespace OQ14.ModalDrivenFarB
open Complex OQ14.ModalDrivenFar

theorem scaled_xi (k r : ℝ) (hk : k ≠ 0) (hr : r ≠ 0) :
    MaxwellFarField.factor k r * ModalAlgebra.xi 1 ((k : ℂ)*r) / (r : ℂ)^2 =
      -(1+I/((k : ℂ)*r))/(r : ℂ) := by
  have hk' : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have hex : exp (-I * (k : ℂ) * (r : ℂ)) * exp (I * ((k : ℂ) * r)) = 1 := by
    rw [← exp_add]; convert exp_zero using 1 <;> ring
  calc
    _ = (-(1+I/((k : ℂ)*r))/(r : ℂ)) *
        (exp (-I * (k : ℂ) * r) * exp (I * ((k : ℂ) * r))) := by
      unfold MaxwellFarField.factor ModalAlgebra.xi
      rw [ModalAlgebra.p_one]
      norm_num
      field_simp [hk', hr']
      ring
    _ = _ := by rw [hex, mul_one]

theorem scaled_outerB (k r : ℝ) (b : ℂ) (hk : k ≠ 0) (hr : r ≠ 0) :
    MaxwellFarField.factor k r * (r : ℂ)^2 * ModalProfiles.outerB (k : ℂ) b r =
      b * (-2*(1+I/((k : ℂ)*r))/(r : ℂ) + (k : ℂ)*(I - 1/((k : ℂ)*r) - I/((k : ℂ)*r)^2)) := by
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  have he : MaxwellFarField.factor k r * (r : ℂ)^2 * ModalProfiles.outerB (k : ℂ) b r =
      2*b*(MaxwellFarField.factor k r * ModalAlgebra.xi 1 ((k : ℂ)*r) / (r : ℂ)^2) -
        MaxwellFarField.factor k r * ModalProfiles.outerA (k : ℂ) b r := by
    unfold ModalProfiles.outerB ModalProfiles.outerA
    field_simp [hr']
    ring
  rw [he, scaled_xi k r hk hr, scaled_outerA k r b hk hr]
  ring
#print axioms OQ14.ModalDrivenFarB.scaled_outerB
end OQ14.ModalDrivenFarB
