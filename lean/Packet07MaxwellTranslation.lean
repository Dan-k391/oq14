import Packet07ScaleMeasure
import KernelConvolution

/-! Literal translations of the weak material Maxwell system. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07MaxwellTranslation
open MeasureTheory Maxwell MaterialMaxwell DynamicSource MagneticResponse KernelConvolution

/-- Translation of the exact weak dielectric Maxwell equations. -/
theorem testMaxwell_translate (k : ℝ) (ε : Maxwell.Space → ℝ) (E H : Maxwell.Field)
    (hM : TestMaxwell k ε E H) (a : Maxwell.Space) :
    TestMaxwell k (fun x => ε (x-a)) (fun x => E (x-a)) (fun x => H (x-a)) := by
  have hp (F : Maxwell.Field) (i : Fin 3) (f : Test) :
      fieldPair (fun x => F (x-a)) i f = fieldPair F i (translate a f) := by
    unfold fieldPair
    exact (translated_pairing (fun x => F x i) a f).symm
  have hc (F : Maxwell.Field) (i : Fin 3) (f : Test) :
      curlPair (fieldPair (fun x => F (x-a))) i f = curlPair (fieldPair F) i (translate a f) := by
    unfold curlPair
    rw [hp, hp, translate_partial, translate_partial]
  intro i f
  have h := hM i (translate a f)
  constructor
  · rw [hc, hp]
    exact h.1
  · rw [hc]
    have hi : (∫ x, ((ε (x-a) : ℝ) : ℂ) * E (x-a) i * f.val x) =
        ∫ x, ((ε x : ℝ) : ℂ) * E x i * (translate a f).val x := by
      exact (translated_pairing (fun x => ((ε x : ℝ) : ℂ) * E x i) a f).symm
    rw [hi]
    exact h.2

end OQ14.Packet07MaxwellTranslation
#print axioms OQ14.Packet07MaxwellTranslation.testMaxwell_translate
