import Packet05ScalarTransmissionH1

/-! Reconstruct the physical electric field on either constant phase from
continuous graph-tangential derivatives and conserved normal displacement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05GraphTransmissionReconstruction
open OQ14.Maxwell

def normalGradient (a b : ℝ) (ε t0 t1 n w0 w1 w2 : ℂ) : ℂ :=
  ((1 + a^2 + b^2 : ℝ) : ℂ)⁻¹ *
    (ε⁻¹*n + (a : ℂ)*t0 + (b : ℂ)*t1 - w2 + (a : ℂ)*w0 + (b : ℂ)*w1)

def physicalField (a b : ℝ) (ε t0 t1 n w0 w1 w2 : ℂ) (i : Fin 3) : ℂ :=
  let t2 := normalGradient a b ε t0 t1 n w0 w1 w2
  if i = 0 then t0-(a : ℂ)*t2+w0
  else if i = 1 then t1-(b : ℂ)*t2+w1
  else t2+w2

theorem normal_gradient_recovery (a b : ℝ) (ε t0 t1 t2 w0 w1 w2 : ℂ) (hε : ε ≠ 0) :
    normalGradient a b ε t0 t1
      (ε * (-(a : ℂ)*t0-(b : ℂ)*t1 +
        ((1+a^2+b^2 : ℝ) : ℂ)*t2 + w2-(a : ℂ)*w0-(b : ℂ)*w1)) w0 w1 w2 = t2 := by
  have hA : (((1+a^2+b^2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1+a^2+b^2 by positivity))
  unfold normalGradient
  push_cast at hA ⊢
  field_simp
  ring

theorem reconstructed_field_continuous
    (a b : Space → ℝ) (ε : ℂ) (t0 t1 n w0 w1 w2 : Space → ℂ)
    (ha : Continuous a) (hb : Continuous b) (ht0 : Continuous t0) (ht1 : Continuous t1)
    (hn : Continuous n) (hw0 : Continuous w0) (hw1 : Continuous w1) (hw2 : Continuous w2)
    (i : Fin 3) : Continuous (fun x => physicalField (a x) (b x) ε
      (t0 x) (t1 x) (n x) (w0 x) (w1 x) (w2 x) i) := by
  have hA : Continuous (fun x => (((1+(a x)^2+(b x)^2 : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.comp ((continuous_const.add (ha.pow 2)).add (hb.pow 2))
  have hAne : ∀ x, (((1+(a x)^2+(b x)^2 : ℝ) : ℂ)) ≠ 0 := by
    intro x
    exact_mod_cast (ne_of_gt (show 0 < 1+(a x)^2+(b x)^2 by positivity))
  have haC := Complex.continuous_ofReal.comp ha
  have hbC := Complex.continuous_ofReal.comp hb
  have hnormal : Continuous (fun x => normalGradient (a x) (b x) ε
      (t0 x) (t1 x) (n x) (w0 x) (w1 x) (w2 x)) := by
    exact (hA.inv₀ hAne).mul (((((continuous_const.mul hn).add (haC.mul ht0)).add
      (hbC.mul ht1)).sub hw2).add (haC.mul hw0) |>.add (hbC.mul hw1))
  fin_cases i <;> simp only [physicalField, Fin.isValue, ↓reduceIte]
  · exact ((ht0.sub (haC.mul hnormal)).add hw0)
  · exact ((ht1.sub (hbC.mul hnormal)).add hw1)
  · exact hnormal.add hw2

end OQ14.Packet05GraphTransmissionReconstruction
#print axioms OQ14.Packet05GraphTransmissionReconstruction.normal_gradient_recovery
#print axioms OQ14.Packet05GraphTransmissionReconstruction.reconstructed_field_continuous
