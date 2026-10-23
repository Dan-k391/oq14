import ConicalProjectionData
import ConicalRadialParticular

/-! Genuine linearity of the endpoint-integrable conical variation-of-constants formula. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ConicalParticularLinear
open MeasureTheory Set OQ14.ConePowerPrimitive OQ14.ConicalRadialParticular
open scoped Topology

theorem primitive_sub (β : ℝ) (hβ : -1 < β) (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0)) (r : ℝ) (hr : 0 ≤ r) :
    primitive β (f-g) r=primitive β f r-primitive β g r := by
  have he : (fun t : ℝ => ((t^β : ℝ) : ℂ)*(f-g) t)=
      (fun t : ℝ => ((t^β : ℝ) : ℂ)*f t-((t^β : ℝ) : ℂ)*g t) := by
    ext t
    simp only [Pi.sub_apply,mul_sub]
  simp only [primitive,he]
  exact intervalIntegral.integral_sub (integrand_intervalIntegrable β hβ f hf r hr)
    (integrand_intervalIntegrable β hβ g hg r hr)

theorem particular_sub (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B C D : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (hC : ContinuousOn C (Ici 0)) (hD : ContinuousOn D (Ici 0)) (r : ℝ) (hr : 0 ≤ r) :
    particular ν (A-C) (B-D) r=particular ν A B r-particular ν C D r := by
  have hm : minusForcing ν (A-C) (B-D)=minusForcing ν A B-minusForcing ν C D := by
    ext t
    simp only [minusForcing,Pi.sub_apply]
    ring
  have hp : plusForcing ν (A-C) (B-D)=plusForcing ν A B-plusForcing ν C D := by
    ext t
    simp only [plusForcing,Pi.sub_apply]
    ring
  have hL := primitive_sub (-ν) (by linarith [hν.2])
    (minusForcing ν A B) (minusForcing ν C D)
    (hB.sub (continuousOn_const.mul hA)) (hD.sub (continuousOn_const.mul hC)) r hr
  have hR := primitive_sub (ν+1) (by linarith [hν.1])
    (plusForcing ν A B) (plusForcing ν C D)
    (hB.add (continuousOn_const.mul hA)) (hD.add (continuousOn_const.mul hC)) r hr
  simp only [particular,leftPrimitive,rightPrimitive,hm,hp,hL,hR]
  ring

end OQ14.ConicalParticularLinear

#print axioms OQ14.ConicalParticularLinear.primitive_sub
#print axioms OQ14.ConicalParticularLinear.particular_sub
