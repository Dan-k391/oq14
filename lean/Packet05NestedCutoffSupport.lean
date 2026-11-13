import Packet05NestedChartCutoffs

/-! Support and plateau consequences of the constructed nested chart cutoffs. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05NestedCutoffSupport
open Set Metric Maxwell WeakCurl WeakConservation Packet05NestedChartCutoffs
open scoped Topology

theorem complex_support (q : RealTest univ) :
    tsupport q.complexTest.function=tsupport q.function := by
  simp only [RealTest.complexTest,tsupport,Function.support,ne_eq,Complex.ofReal_eq_zero]

theorem complex_regular (q : RealTest univ) (n : ℕ) (hq : ContDiff ℝ n q.function) :
    ContDiff ℝ n q.complexTest.function := Complex.ofRealCLM.contDiff.comp hq

theorem ball8_subset {Ω : Set Space} {c : Space} (q : Data Ω c) : ball c (8*q.r) ⊆ Ω := by
  intro x hx
  apply q.outer_support
  apply subset_tsupport
  change q.outer.function x ≠ 0
  intro hz
  have hh := (q.outer_one x hx).eq_of_nhds
  change (q.outer.function x : ℂ)=1 at hh
  rw [hz] at hh
  norm_num at hh

theorem small_ball_subset {Ω : Set Space} {c : Space} (q : Data Ω c)
    (a : ℝ) (ha : a ≤ 8) : ball c (a*q.r) ⊆ Ω :=
  (ball_subset_ball (mul_le_mul_of_nonneg_right ha q.positive.le)).trans (ball8_subset q)

theorem middle_support {Ω : Set Space} {c : Space} (q : Data Ω c) :
    tsupport q.middle.function ⊆ Ω := by
  intro x hx
  exact ball8_subset q ((q.shifted_support 0 0 (by simpa using q.positive) x hx).1)

theorem real_one_complex (q : RealTest univ) {x : Space} (h : q.function x=1) :
    q.complexTest.function x=1 := by
  change (q.function x : ℂ)=1
  rw [h,Complex.ofReal_one]

end OQ14.Packet05NestedCutoffSupport
#print axioms OQ14.Packet05NestedCutoffSupport.complex_support
#print axioms OQ14.Packet05NestedCutoffSupport.complex_regular
#print axioms OQ14.Packet05NestedCutoffSupport.ball8_subset
#print axioms OQ14.Packet05NestedCutoffSupport.small_ball_subset
#print axioms OQ14.Packet05NestedCutoffSupport.middle_support
#print axioms OQ14.Packet05NestedCutoffSupport.real_one_complex
