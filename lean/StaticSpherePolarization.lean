import StaticBallNewton

/-! # Exact isolated static sphere polarization

The source is a genuine constant-ball L2 field. Its literal static equation
is derived from the already proved Newton action, rather than from an
assumed depolarization identity.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticSpherePolarization

open MeasureTheory Metric Set StaticBallNewton
open scoped Topology

def polarization (χ : ℝ) (E : Vector) : Vector :=
  ((3*χ/(χ+3) : ℝ) : ℂ) • E

theorem polarization_identity (χ : ℝ) (hχ : 0 ≤ χ) (E : Vector) (i : Fin 3) :
    polarization χ E i = (χ : ℂ) * (E i - polarization χ E i / 3) := by
  have hd : ((χ : ℂ)+3) ≠ 0 := by
    have hh : χ+3 ≠ 0 := by linarith
    exact_mod_cast hh
  change ((3*χ/(χ+3) : ℝ) : ℂ) * E i =
    (χ : ℂ)*(E i-((3*χ/(χ+3) : ℝ) : ℂ)*E i/3)
  push_cast
  field_simp [hd]
  ring

theorem interior_field_factor (R : ℝ) (hR : 0 < R) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : Vector) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) R →
      E i + NewtonL2.newtonOperator (source R (polarization χ E))
        (VectorFourier.coordinateMap x) i = ((3/(χ+3) : ℝ) : ℂ) * E i := by
  filter_upwards [newton_source_interior R hR (polarization χ E) i] with x hx hm
  rw [hx hm]
  have hd : ((χ : ℂ)+3) ≠ 0 := by
    have hh : χ+3 ≠ 0 := by linarith
    exact_mod_cast hh
  change E i + -(((3*χ/(χ+3) : ℝ) : ℂ)*E i)/3 = _
  push_cast
  field_simp [hd]
  ring

theorem exact_static_equation (R : ℝ) (hR : 0 < R) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : Vector) (i : Fin 3) :
    (fun x => source R (polarization χ E) (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      (ball (0 : Space) R).indicator (fun x => (χ : ℂ) *
        (E i + NewtonL2.newtonOperator (source R (polarization χ E))
          (VectorFourier.coordinateMap x) i)) := by
  filter_upwards [source_ae R (polarization χ E) i,
    newton_source_interior R hR (polarization χ E) i] with x hs hn
  rw [hs]
  by_cases hm : x ∈ ball (0 : Space) R
  · rw [indicator_of_mem hm, indicator_of_mem hm, hn hm]
    simpa only [sub_eq_add_neg, neg_div] using polarization_identity χ hχ E i
  · rw [indicator_of_not_mem hm, indicator_of_not_mem hm]

theorem permittivity_factor (ε : ℝ) (E : Vector) :
    polarization (ε-1) E = (((ε-1)*3/(ε+2) : ℝ) : ℂ) • E := by
  unfold polarization
  congr 2
  ring

end OQ14.StaticSpherePolarization

#print axioms OQ14.StaticSpherePolarization.polarization_identity
#print axioms OQ14.StaticSpherePolarization.interior_field_factor
#print axioms OQ14.StaticSpherePolarization.exact_static_equation
#print axioms OQ14.StaticSpherePolarization.permittivity_factor
