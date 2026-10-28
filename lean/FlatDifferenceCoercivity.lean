import MaxwellWeakTranslation
import MaxwellInverseCurlCurl

/-! The precise positive jump coefficient for flat tangential quotient energy. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.FlatDifferenceCoercivity
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.MaxwellWeakTranslation

def dielectric (d : ℝ) (x : Space) : ℝ := if x 2 < 0 then 1 else 1+d

theorem dielectric_measurable (d : ℝ) : Measurable (dielectric d) := by
  unfold dielectric
  exact measurable_const.piecewise
    (measurableSet_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous.measurable measurable_const)
    measurable_const

theorem dielectric_bounds (d : ℝ) (hd : 0 ≤ d) (x : Space) :
    1 ≤ dielectric d x ∧ dielectric d x ≤ 1+d := by
  unfold dielectric
  split_ifs <;> constructor <;> linarith

theorem flatWeight_eq_inverse (d : ℝ) (x : Space) :
    flatWeight d x = (((dielectric d x)⁻¹ : ℝ) : ℂ) := by
  unfold flatWeight dielectric
  split_ifs <;> simp

theorem quotient_curl_energy (C : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (i j : Fin 3) (h : ℝ) :
    (1+d)⁻¹ * (∫ x, ‖quotientVector C i h j x‖^2) ≤
      ∫ x, (dielectric d x)⁻¹ * ‖quotientVector C i h j x‖^2 := by
  have h := MaxwellInverseCurlCurl.inverse_weight_coercivity (Ω := Set.univ)
    (dielectric d) (1+d) (dielectric_measurable d)
    (fun x => (dielectric_bounds d hd x).1) (fun x => (dielectric_bounds d hd x).2)
    (fun x => quotientVector C i h j x) (by simpa [DomainCurl.regionMeasure] using Lp.memLp (quotientVector C i h j))
  simpa using h

end OQ14.FlatDifferenceCoercivity
#print axioms OQ14.FlatDifferenceCoercivity.quotient_curl_energy
