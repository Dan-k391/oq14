import ComplexSphereWeak

noncomputable section
set_option autoImplicit false
namespace OQ14.CompactSmoothSchwartz
open MeasureTheory Metric Set OQ14.Maxwell
open scoped SchwartzMap Topology

def ofCompact (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) : 𝓢(Space, ℂ) where
  toFun := φ
  smooth' := hφ
  decay' := by
    intro k m
    have hcont : Continuous (fun x : Space => ‖x‖^k * ‖iteratedFDeriv ℝ m φ x‖) :=
      (continuous_norm.pow k).mul (((hφ.of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)) : ContDiff ℝ (m : ℕ) φ).continuous_iteratedFDeriv le_rfl).norm)
    obtain ⟨C,hC⟩ := hc.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, fun x => ?_⟩
    by_cases hx : x ∈ tsupport φ
    · exact (le_abs_self _).trans ((hC x hx).trans (le_max_left _ _))
    · have hz : iteratedFDeriv ℝ m φ x = 0 := by
        apply image_eq_zero_of_nmem_tsupport
        exact fun h => hx (tsupport_iteratedFDeriv_subset m h)
      simp [hz, le_max_right]

@[simp] theorem ofCompact_apply (φ : Space → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (x : Space) : ofCompact φ hφ hc x = φ x := rfl

#print axioms OQ14.CompactSmoothSchwartz.ofCompact
end OQ14.CompactSmoothSchwartz



