import Packet06ComplexHessian
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ResponseLinear
open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

theorem pairing_sub (q₁ q₂ ρ : Space → ℂ) (h₁ : LocallyIntegrable q₁) (h₂ : LocallyIntegrable q₂)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : Test) :
    (∫ x, response (fun x => q₁ x - q₂ x) ρ x * f.val x) =
      (∫ x, response q₁ ρ x * f.val x) - (∫ x, response q₂ ρ x * f.val x) := by
  have hsub : LocallyIntegrable (fun x => q₁ x - q₂ x) := h₁.sub h₂
  rw [response_pairing _ ρ hsub hρ hc f, response_pairing _ ρ h₁ hρ hc f,
    response_pairing _ ρ h₂ hρ hc f]
  rw [← integral_sub (source_pairing_integrable q₁ ρ h₁ hρ hc f)
    (source_pairing_integrable q₂ ρ h₂ hρ hc f)]
  apply integral_congr_ae
  filter_upwards with y
  rw [← translated_pairing (fun x => q₁ x-q₂ x) y f, ← translated_pairing q₁ y f,
    ← translated_pairing q₂ y f]
  have hi₁ := PointSingularity.test_product_integrable q₁ (translate y f).val h₁
    (translate y f).val.continuous (translate y f).property
  have hi₂ := PointSingularity.test_product_integrable q₂ (translate y f).val h₂
    (translate y f).val.continuous (translate y f).property
  simp only [sub_mul, integral_sub hi₁ hi₂, mul_sub]

theorem pairing_const_mul (a : ℂ) (q ρ : Space → ℂ) (hq : LocallyIntegrable q)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : Test) :
    (∫ x, response (fun x => a * q x) ρ x * f.val x) =
      a * (∫ x, response q ρ x * f.val x) := by
  have ha : LocallyIntegrable (fun x => a * q x) := by simpa only [smul_eq_mul] using hq.smul a
  rw [response_pairing _ ρ ha hρ hc f, response_pairing _ ρ hq hρ hc f, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← translated_pairing (fun x => a*q x) y f, ← translated_pairing q y f]
  simp only [mul_assoc, integral_const_mul]
  ring

theorem dynamic_pairing (z : ℂ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i j : Fin 3) (f : Test) :
    (∫ x, response (fun x => ComplexDynamicKernel.remainder z x i j) ρ x * f.val x) =
      z^2 * (if i = j then 1 else 0) * Packet06ComplexPotentialPair.potentialPair z ρ f +
        Packet06ComplexPotentialPair.potentialPair z ρ (testPartial j (testPartial i f)) -
        Packet06ComplexPotentialPair.potentialPair 0 ρ (testPartial j (testPartial i f)) := by
  have hphi := Packet06ComplexScalarKernel.phi_locallyIntegrable z
  let a : ℂ := z^2 * (if i = j then 1 else 0)
  have ha : LocallyIntegrable (fun x => a * ComplexGreenKernel.phi z x) := by
    simpa only [smul_eq_mul] using hphi.smul a
  have hh := Packet06ComplexHessian.hessian_pairing z ρ hρ hc i j f
  have heq : (fun x => Packet06ComplexHessian.hessianDifference z x i j) =
      (fun x => ComplexDynamicKernel.remainder z x i j - a * ComplexGreenKernel.phi z x) := by
    funext x
    simp only [Packet06ComplexHessian.hessianDifference, a]
    ring
  rw [heq, pairing_sub _ _ ρ (ComplexDynamicKernel.remainder_locallyIntegrable z i j) ha hρ hc f,
    pairing_const_mul a _ ρ hphi hρ hc f,
    Packet06ComplexPotentialPair.potential_pairing z ρ hρ hc f] at hh
  have hg : (fun x => ComplexMagneticAnalytic.gradientDifference z x j) =
      (fun x => ComplexGreenKernel.phiGradient z x j - ComplexGreenKernel.phiGradient 0 x j) := rfl
  rw [hg, pairing_sub _ _ ρ (ComplexMagneticLocal.gradient_locallyIntegrable z j)
    (ComplexMagneticLocal.gradient_locallyIntegrable 0 j) hρ hc (testPartial i f),
    Packet06ComplexPotentialPair.gradient_pairing z ρ hρ hc j (testPartial i f),
    Packet06ComplexPotentialPair.gradient_pairing 0 ρ hρ hc j (testPartial i f)] at hh
  dsimp only [a] at hh
  linear_combination hh

#print axioms OQ14.Packet06ResponseLinear.pairing_sub
#print axioms OQ14.Packet06ResponseLinear.pairing_const_mul
#print axioms OQ14.Packet06ResponseLinear.dynamic_pairing
end OQ14.Packet06ResponseLinear
