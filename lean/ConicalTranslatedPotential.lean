import ConicalCommonLocal

/-! Translate locally L² weak potential data to tip-centered coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalTranslatedPotential
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalGradientGraph
open scoped SchwartzMap Topology
abbrev Space := Maxwell.Space

theorem memLp_translate (f : Space → ℂ)
    (hf : ∀ R : ℝ, MemLp f 2 (volume.restrict (closedBall (0 : Space) R)))
    (c : Space) (R : ℝ) : MemLp (fun x => f (x + c)) 2 (volume.restrict (closedBall (0 : Space) R)) := by
  let T := max R 0 + ‖c‖
  have hbig := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (hf T)
  have htrans := hbig.comp_measurePreserving (measurePreserving_add_right (volume : Measure Space) c)
  have hres := htrans.mono_measure (Measure.restrict_le_self : volume.restrict (closedBall (0 : Space) R) ≤ volume)
  apply (memLp_congr_ae ?_).mp hres
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  have hxnorm : ‖x‖ ≤ R := by simpa using hx
  have hmem : x + c ∈ closedBall (0 : Space) T := by
    simp only [mem_closedBall, dist_zero_right]
    exact (norm_add_le x c).trans (add_le_add_right (hxnorm.trans (le_max_left _ _)) _)
  simp [Function.comp_def, hmem]

def translated (c : Space) (u : PotentialData) : PotentialData where
  potential x := u.potential (x + c)
  derivative i x := u.derivative i (x + c)
  potential_memLp R := memLp_translate u.potential u.potential_memLp c R
  derivative_memLp R i := memLp_translate (u.derivative i) (fun R => u.derivative_memLp R i) c R
  weak i f := by
    let g : DynamicSource.Test := ⟨NewtonConvolution.translate (-c) f.val, by
      change HasCompactSupport (fun x => f.val (x + -c))
      exact f.property.comp_homeomorph (Homeomorph.addRight (-c))⟩
    have h := u.weak i g
    have hp := integral_add_right_eq_self (μ := (volume : Measure Space))
      (fun x => u.potential x * (DynamicSource.testPartial i g).val x) c
    have hd := integral_add_right_eq_self (μ := (volume : Measure Space))
      (fun x => u.derivative i x * g.val x) c
    rw [← hp, ← hd] at h
    simpa [g, DynamicSource.testPartial, NewtonConvolution.translate_pderivative,
      NewtonConvolution.translate_apply] using h

end OQ14.ConicalTranslatedPotential
#print axioms OQ14.ConicalTranslatedPotential.memLp_translate
#print axioms OQ14.ConicalTranslatedPotential.translated
