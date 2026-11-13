import Packet05FiveNestedCutoffs

/-! Exact inclusions and plateaus for the five-cutoff scalar/physical layout. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05FiveCutoffLayout
open Set Metric Maxwell WeakCurl WeakConservation Packet05NestedCutoffSupport Packet05FiveNestedCutoffs

theorem layout {Ω : Set Space} {p : Space} (q : Data Ω p) :
    let Sboot := ball p (2*q.q0.r)
    let Viter := ball p (4*q.q1.r)
    let Siter := ball p (2*q.q1.r)
    let Vlocal := ball p (2*q.q2.r)
    let Vreg := ball p (4*q.q3.r)
    let Wreg := ball p (4*q.q4.r)
    let T := ball p (2*q.q4.r)
    Viter ⊆ Sboot ∧ Siter ⊆ Viter ∧ Vlocal ⊆ Siter ∧ Vreg ⊆ Vlocal ∧
    Wreg ⊆ Vreg ∧ T ⊆ Wreg ∧
    tsupport q.q3.outer.function ⊆ Vlocal ∧
    tsupport q.q3.middle.function ⊆ Vlocal ∧
    tsupport q.q4.outer.function ⊆ Vreg ∧
    tsupport q.q4.inner.function ⊆ Wreg ∧
    (∀ x ∈ Vlocal, q.q1.inner.function x = 1) ∧
    (∀ x ∈ Vlocal, q.q2.middle.function x = 1) ∧
    (∀ x ∈ Vreg, q.q3.outer.complexTest.function x = 1) ∧
    (∀ x ∈ T, q.q3.middle.function x = 1) ∧
    (∀ x ∈ Wreg, q.q4.outer.complexTest.function x = 1) ∧
    (∀ x ∈ T, q.q4.inner.function x = 1) ∧
    (∀ x ∈ T, q.q0.inner.function x = 1) := by
  dsimp only
  have h1 : ball p (4*q.q1.r) ⊆ ball p (2*q.q0.r) := small_ball_subset q.q1 4 (by norm_num)
  have h2 : ball p (2*q.q1.r) ⊆ ball p (4*q.q1.r) := ball_subset_ball (by linarith [q.q1.positive])
  have h3 : ball p (2*q.q2.r) ⊆ ball p (2*q.q1.r) := small_ball_subset q.q2 2 (by norm_num)
  have h4 : ball p (4*q.q3.r) ⊆ ball p (2*q.q2.r) := small_ball_subset q.q3 4 (by norm_num)
  have h5 : ball p (4*q.q4.r) ⊆ ball p (4*q.q3.r) := small_ball_subset q.q4 4 (by norm_num)
  have h6 : ball p (2*q.q4.r) ⊆ ball p (4*q.q4.r) := ball_subset_ball (by linarith [q.q4.positive])
  have hTreg := h6.trans h5
  have hTlocal := hTreg.trans h4
  have hTiter := hTlocal.trans h3
  have hTboot := hTiter.trans (h2.trans h1)
  refine ⟨h1,h2,h3,h4,h5,h6,q.q3.outer_support,middle_support q.q3,
    q.q4.outer_support,q.q4.inner_middle,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact (q.q1.inner_one x (h3 hx)).eq_of_nhds
  · intro x hx
    exact q.q2.middle_one x ((ball_subset_ball (show 2*q.q2.r ≤ 4*q.q2.r by linarith [q.q2.positive])) hx)
  · intro x hx
    exact (q.q3.outer_one x ((ball_subset_ball (show 4*q.q3.r ≤ 8*q.q3.r by linarith [q.q3.positive])) hx)).eq_of_nhds
  · intro x hx
    exact q.q3.middle_one x (hTreg hx)
  · intro x hx
    exact (q.q4.outer_one x ((ball_subset_ball (show 4*q.q4.r ≤ 8*q.q4.r by linarith [q.q4.positive])) hx)).eq_of_nhds
  · intro x hx
    exact (q.q4.inner_one x hx).eq_of_nhds
  · intro x hx
    exact (q.q0.inner_one x (hTboot hx)).eq_of_nhds

end OQ14.Packet05FiveCutoffLayout
#print axioms OQ14.Packet05FiveCutoffLayout.layout
