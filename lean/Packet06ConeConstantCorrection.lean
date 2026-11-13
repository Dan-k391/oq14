import ConicalRadialParticular
import ConicalMomentWeights
import SphereCapWeak
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeConstantCorrection
open MeasureTheory Set OQ14.ConicalRadialParticular OQ14.ConePowerPrimitive

theorem primitive_constant (β : ℝ) (hβ : -1 < β) (A : ℂ) (r : ℝ) (_hr : 0 ≤ r) :
    primitive β (fun _ => A) r = ((r^(β+1)/(β+1) : ℝ) : ℂ) * A := by
  unfold primitive
  rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_ofReal, integral_rpow (Or.inl hβ)]
  simp [Real.zero_rpow (by linarith : β+1 ≠ 0)]

theorem constant_particular (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A : ℂ) (r : ℝ) (hr : 0 < r) :
    particular ν (fun _ => A) (fun _ => ((ν*(ν+1) : ℝ) : ℂ)*A) r = -(r : ℂ)*A := by
  have h1 : (-ν : ℝ)+1 ≠ 0 := by linarith [hν.2]
  have h2 : ν+1+1 ≠ 0 := by linarith [hν.1]
  have h3 : 2*ν+1 ≠ 0 := by linarith [hν.1]
  unfold particular leftPrimitive rightPrimitive minusForcing plusForcing
  rw [primitive_constant (-ν) (by linarith [hν.2]) _ r hr.le,
    primitive_constant (ν+1) (by linarith [hν.1]) _ r hr.le]
  have hp1 : power ν r * power (-ν+1) r = (r : ℂ) := by
    rw [power_mul _ _ _ hr]
    simp [show ν + (-ν+1) = 1 by ring, power]
  have hp2 : power (-ν-1) r * power (ν+2) r = (r : ℂ) := by
    rw [power_mul _ _ _ hr]
    simp [show -ν-1 + (ν+2) = 1 by ring, power]
  have h1c : -(ν : ℂ) + 1 ≠ 0 := by exact_mod_cast h1
  have h2c : (ν : ℂ) + 1 + 1 ≠ 0 := by exact_mod_cast h2
  have h3c : 2*(ν : ℂ) + 1 ≠ 0 := by exact_mod_cast h3
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_neg,
    Complex.ofReal_mul, Complex.ofReal_ofNat, power] at *
  push_cast at *
  field_simp [h1c,h2c,h3c]
  ring_nf at hp1 hp2 ⊢
  linear_combination (norm := ring_nf) (A * (2*(ν : ℂ)^2 + (ν : ℂ)^3 - (ν : ℂ) - 2) * hp1) + (A * (-2*(ν : ℂ) + (ν : ℂ)^2 + (ν : ℂ)^3) * hp2)
theorem angular_constant_identity (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : OQ14.CapAngularShooting.determinant d t a = 0) (i : Fin 3) :
    (∫ n : OQ14.AngularPower.Sphere, OQ14.CapSturmLiouville.coefficient d t ((n : OQ14.Maxwell.Space) 2) *
      OQ14.SphereCapH1.gradient a t n i ∂OQ14.AngularPower.angularMeasure) =
    a * ∫ n : OQ14.AngularPower.Sphere, OQ14.CapSturmLiouville.coefficient d t ((n : OQ14.Maxwell.Space) 2) *
      OQ14.SphereCapH1.field a t n * (n : OQ14.Maxwell.Space) i ∂OQ14.AngularPower.angularMeasure := by
  have h := OQ14.SphereCapH1.field_weighted_weak a d t ha ht ht1 hroot
    (fun x : OQ14.Maxwell.Space => x i) ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)
  have he : (fun x : OQ14.Maxwell.Space => x i) = (EuclideanSpace.proj (𝕜 := ℝ) i) := rfl
  rw [he] at h
  simp only [ContinuousLinearMap.fderiv] at h
  change (∫ n : OQ14.AngularPower.Sphere, OQ14.CapSturmLiouville.coefficient d t ((n : OQ14.Maxwell.Space) 2) * OQ14.SphereCapH1.gradient a t n i ∂OQ14.AngularPower.angularMeasure) =
    a * ∫ n : OQ14.AngularPower.Sphere, OQ14.CapSturmLiouville.coefficient d t ((n : OQ14.Maxwell.Space) 2) * (OQ14.SphereCapH1.field a t n * (n : OQ14.Maxwell.Space) i) ∂OQ14.AngularPower.angularMeasure at h
  simpa only [mul_assoc] using h
#print axioms OQ14.Packet06ConeConstantCorrection.primitive_constant
#print axioms OQ14.Packet06ConeConstantCorrection.constant_particular
#print axioms OQ14.Packet06ConeConstantCorrection.angular_constant_identity
end OQ14.Packet06ConeConstantCorrection
