import FreeSourceCoefficients
import AngularExteriorBounds
import HankelExteriorBounds

/-! Actual canonical outgoing vacuum vector modes with explicit angular-radial bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VacuumOutgoingBounds
open Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
open OQ14.SourceFarAmplitude OQ14.SourceRadiation OQ14.ModalAlgebra OQ14.AngularExteriorBounds

def data (l : ℕ) : SourceRadialSystem.Data where
  l := l
  gs := []
  R := 1
  X := 1
  c := 1
  hR := zero_lt_one
  hc := zero_lt_one
  chain := RadialStack.Chain.nil 1

theorem amplitude_value (l : ℕ) : amplitude (data l)= -I := by
  exact FreeSourceCoefficients.vacuum_amplitude (data l)

theorem phase_norm (l : ℕ) : ‖phase l‖=1 := by simp [phase,norm_pow]

theorem p_norm (l : ℕ) (r : ℝ) : ‖p l r‖=‖xi l r‖ := by
  simp [xi,norm_mul,norm_pow,Complex.norm_exp]

theorem p_derivative_norm (l : ℕ) (r : ℝ) : ‖I*p l r+pD l r‖=‖xiD l r‖ := by
  simp [xiD,norm_mul,norm_pow,Complex.norm_exp]

theorem electric_weighted_bound (l : ℕ) (m : Index l) (n : Sphere) (r : ℝ) (hr : 1<r) (i : Fin 3) :
    ‖electricWeighted (data l) (representative l m) (r • (n : Space)) i‖≤
      (l+1 : ℝ)^2*envelope l*(‖xiD l r‖+‖xi l r‖) := by
  have he := congrFun (electric_ray (data l) (representative l m)
    (representative_homogeneous l m) n r (zero_lt_one.trans hr) hr) i
  rw [he]
  simp only [show (data l).l=l from rfl,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  apply (norm_add_le _ _).trans
  have hnorm : ‖(l : ℂ)+1‖=(l : ℝ)+1 := by simpa only [Nat.cast_add,Nat.cast_one] using Complex.norm_natCast (l+1)
  simp only [norm_mul,amplitude_value,phase_norm,norm_neg,norm_I,one_mul,norm_div,hnorm,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hr),Complex.norm_natCast]
  rw [p_norm,p_derivative_norm]
  have h1 := AngularExteriorBounds.poloidal_bound l m n i
  have h2 := AngularExteriorBounds.radial_bound l m n i
  have hratio : ‖xi l r‖/r≤‖xi l r‖ := div_le_self (norm_nonneg _) hr.le
  have hl : 0≤(l : ℝ) := Nat.cast_nonneg l
  have ha : 0≤envelope l := envelope_nonnegative l
  have hp : (l+1 : ℝ)≤(l+1 : ℝ)^2 := by nlinarith
  have hp' : (l : ℝ)*(l+1)≤(l+1 : ℝ)^2 := by nlinarith
  have ht1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg (xiD l r))
  have ht2 : (l : ℝ)*(l+1)*(‖xi l r‖/r)*‖HarmonicRadiationFactors.radial (representative l m) n i‖≤
      (l : ℝ)*(l+1)*‖xi l r‖*envelope l :=
    mul_le_mul (mul_le_mul_of_nonneg_left hratio (mul_nonneg hl (by positivity))) h2
      (norm_nonneg _) (mul_nonneg (mul_nonneg hl (by positivity)) (norm_nonneg _))
  calc
    _ ≤ ‖xiD l r‖*((l+1 : ℝ)*envelope l)+(l : ℝ)*(l+1)*‖xi l r‖*envelope l :=
      add_le_add ht1 ht2
    _ ≤ ‖xiD l r‖*((l+1 : ℝ)^2*envelope l)+(l+1 : ℝ)^2*‖xi l r‖*envelope l := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp ha) (norm_nonneg _)
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp' (norm_nonneg _)) ha
    _ = _ := by ring

theorem magnetic_weighted_bound (l : ℕ) (m : Index l) (n : Sphere) (r : ℝ) (hr : 1<r) (i : Fin 3) :
    ‖magneticWeighted (data l) (representative l m) (r • (n : Space)) i‖≤
      2*envelope l*‖xi l r‖ := by
  have he := congrFun (magnetic_ray (data l) (representative l m)
    (representative_homogeneous l m) n r (zero_lt_one.trans hr) hr) i
  rw [he]
  simp only [show (data l).l=l from rfl,Pi.smul_apply,smul_eq_mul,norm_mul,amplitude_value,phase_norm,norm_neg,norm_I,one_mul]
  rw [p_norm]
  exact (mul_le_mul_of_nonneg_left (AngularExteriorBounds.toroidal_bound l m n i)
    (norm_nonneg _)).trans_eq (by ring)

end OQ14.VacuumOutgoingBounds

#print axioms OQ14.VacuumOutgoingBounds.amplitude_value
#print axioms OQ14.VacuumOutgoingBounds.phase_norm
#print axioms OQ14.VacuumOutgoingBounds.p_norm
#print axioms OQ14.VacuumOutgoingBounds.p_derivative_norm
#print axioms OQ14.VacuumOutgoingBounds.electric_weighted_bound
#print axioms OQ14.VacuumOutgoingBounds.magnetic_weighted_bound
