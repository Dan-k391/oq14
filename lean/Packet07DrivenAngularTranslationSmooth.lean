import Packet07DrivenFrameAngularSmooth
import Packet07AngularTranslation

/-! Translation preserves smooth extensions of arbitrary angular densities. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenAngularTranslationSmooth
open Maxwell SphereHarmonicBasis
open scoped InnerProductSpace
abbrev Space := Maxwell.Space
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def extension (k : ℝ) (a : Space) (F : Fin 3 → Space → ℂ) (i : Fin 3) (x : Space) : ℂ :=
  Complex.exp (((k * ⟪x,a⟫_ℝ : ℝ) : ℂ)*Complex.I)*F i x

theorem extension_smooth (k : ℝ) (a : Space) (F : Fin 3 → Space → ℂ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (extension k a F i) := by
  unfold extension
  apply ContDiff.mul
  · apply Complex.contDiff_exp.comp
    exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
      ((contDiff_id : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space => x)).inner ℝ contDiff_const))).mul contDiff_const)
  · exact hF i

theorem extension_on_sphere (k : ℝ) (a : Space) (F : Fin 3 → Space → ℂ) (A : C(Sphere,Vector))
    (hF : ∀ (n : Sphere) i, F i n=A n i) (n : Sphere) (i : Fin 3) :
    extension k a F i n = Packet07AngularTranslation.translatedAmplitude k a A n i := by
  change Complex.exp (((k * ⟪(n : Space),a⟫_ℝ : ℝ) : ℂ)*Complex.I)*F i n =
    SphereReactionKernel.wave k a n * A n i
  rw [hF]
  rfl
end OQ14.Packet07DrivenAngularTranslationSmooth
#print axioms OQ14.Packet07DrivenAngularTranslationSmooth.extension_smooth
#print axioms OQ14.Packet07DrivenAngularTranslationSmooth.extension_on_sphere
