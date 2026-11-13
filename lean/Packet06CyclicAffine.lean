import Packet06CyclicOutgoing
import Packet06FrequencyPlacement

/-! Combined physical rotation, translation and prescribed complex frequency. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06CyclicAffine
open Maxwell Packet06ComplexAffine Packet06CyclicRotation Packet06CyclicRotationMaxwell

def placedField (s : ℝ) (a : Space) (F : Field) : Field :=
  fun x => rotateField F (s • (x-a))

theorem placed_maxwell (z : ℂ) (s : ℝ) (hs : 0 < s) (a : Space)
    (ε : Space → ℝ) (E H : Field) (hM : TestMaxwellC z ε E H) :
    TestMaxwellC ((s : ℂ)*z) (fun x => ε (unrotate (s • (x-a))))
      (placedField s a E) (placedField s a H) := by
  have hr := complex_maxwell_rotate z ε E H hM
  have hd := dilate z s hs (fun x => ε (unrotate x)) (rotateField E) (rotateField H) hr
  exact translate ((s : ℂ)*z) _ _ _ hd a

theorem placed_frequency (z : ℂ) (target : ℝ) (hz : 0 < z.re) (hdecay : z.im < 0) (ht : 0 < target)
    (a : Space) (ε : Space → ℝ) (E H : Field) (hM : TestMaxwellC z ε E H) :
    ∃ s : ℝ, 0 < s ∧ ((s : ℂ)*z).re = target ∧ ((s : ℂ)*z).im < 0 ∧
      -((s : ℂ)*z).re / (2*((s : ℂ)*z).im) = -z.re / (2*z.im) ∧
      TestMaxwellC ((s : ℂ)*z) (fun x => ε (unrotate (s • (x-a))))
        (placedField s a E) (placedField s a H) := by
  obtain ⟨s,hs,hreal,him,hQ⟩ := Packet06FrequencyPlacement.positive_real_frequency z target hz ht
  exact ⟨s,hs,hreal,by rw [him]; exact mul_neg_of_pos_of_neg hs hdecay,hQ,
    placed_maxwell z s hs a ε E H hM⟩

end OQ14.Packet06CyclicAffine
#print axioms OQ14.Packet06CyclicAffine.placed_maxwell
#print axioms OQ14.Packet06CyclicAffine.placed_frequency
