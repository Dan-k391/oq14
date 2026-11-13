import Packet05ExplicitAnisotropicBound
import Mathlib.MeasureTheory.Measure.OpenPos

/-! The genuine continuous representative of a compact H2 function obeys
the explicit anisotropic bound; no new representative is substituted. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ContinuousH2Bound
open MeasureTheory Maxwell WeakCurl DivCurlCompact Packet05ExplicitAnisotropicBound

theorem continuous_h2_bound (u : L2Scalar) (f : Space → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (huf : (u : Space → ℂ) =ᵐ[volume] f)
    (D : Fin 3 → L2Scalar) (H : Fin 3 → Fin 3 → L2Scalar)
    (hD : ∀ i, HasWeakPartial u (D i) i)
    (hH : ∀ i j, HasWeakPartial (D i) (H i j) j)
    (N : ℝ) (hu : ‖u‖ ≤ N) (hd : ∀ i, ‖D i‖ ≤ N) (hh : ∀ i j, ‖H i j‖ ≤ N) :
    ∀ x, ‖f x‖ ≤ 10*universalConstant*N := by
  obtain ⟨g,hg,hug,hbound⟩ := continuous_sup_bound u ⟨f,hfc,huf⟩ D hD H (fun i _ j => hH i j)
  have he : g=f := Measure.eq_of_ae_eq (hug.symm.trans huf) hg hf
  rw [he] at hbound
  have hsumD : (∑ i : Fin 3, ‖D i‖) ≤ 3*N := by
    simpa only [Fin.sum_univ_three] using add_le_add (add_le_add (hd 0) (hd 1)) (hd 2) |>.trans_eq (by ring)
  have hsumH : (∑ i : Fin 2, ∑ j : Fin 3, ‖H i.castSucc j‖) ≤ 6*N := by
    have hb (i : Fin 2) : (∑ j : Fin 3, ‖H i.castSucc j‖) ≤ 3*N := by
      simp only [Fin.sum_univ_three]
      linarith [hh i.castSucc 0,hh i.castSucc 1,hh i.castSucc 2]
    simp only [Fin.sum_univ_two]
    linarith [hb 0,hb 1]
  have hC : 0 ≤ universalConstant := by unfold universalConstant; positivity
  intro x
  apply (hbound x).trans
  have hdata : ‖u‖+(∑ i : Fin 3, ‖D i‖)+(∑ i : Fin 2, ∑ j : Fin 3, ‖H i.castSucc j‖) ≤ 10*N := by linarith
  exact (mul_le_mul_of_nonneg_left hdata hC).trans_eq (by ring)

end OQ14.Packet05ContinuousH2Bound
#print axioms OQ14.Packet05ContinuousH2Bound.continuous_h2_bound
