import Packet07LobeGeometry

/-! Eventually both rounded double-cone lobes contain explicit axial material points. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07LobeNonempty
open Set Metric Filter
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data

/-- A sufficiently small rounded cap contains either fixed axial midpoint. -/
theorem axial_point_inclusion (n : ℕ) (m a z : ℝ) (ha : 0 < a)
    (hz : |z| = a/2) (he : ConicalTipRounding.radius n < a/4)
    (he2 : (ConicalTipRounding.radius n)^2 < a^3/4) :
    EuclideanSpace.single 2 z ∈ ConicalJunctionPhysical.inclusion n m a := by
  let x : Space := EuclideanSpace.single 2 z
  have hh : ConicalJunctionPhysical.horizontal x = 0 := by
    ext i
    fin_cases i <;> simp [x, ConicalJunctionPhysical.horizontal, EuclideanSpace.single_apply]
  have hx2 : x 2 = z := by simp [x, EuclideanSpace.single_apply]
  have hsquare : z^2 = a^2/4 := by nlinarith [sq_abs z]
  have hc : ConicalSmoothJunction.coneMargin n m (ConicalJunctionPhysical.split x) =
      a/2 - ConicalTipRounding.radius n := by
    simp [ConicalSmoothJunction.coneMargin, ConicalJunctionPhysical.split, hh, hx2, hz,
      ConicalSmoothCapGraph.cap_apex]
  have hb : ConicalSmoothJunction.ballMargin a (ConicalJunctionPhysical.split x) = 3*a^2/4 := by
    simp only [ConicalSmoothJunction.ballMargin, ConicalJunctionPhysical.split, hh, norm_zero, zero_pow,
      sub_zero, hx2]
    nlinarith
  have hcone : 0 < ConicalSmoothJunction.coneMargin n m (ConicalJunctionPhysical.split x) := by rw [hc]; linarith
  have hball : 0 < ConicalSmoothJunction.ballMargin a (ConicalJunctionPhysical.split x) := by rw [hb]; positivity
  have hcorr : ConicalSmoothJunction.correction n
      (ConicalSmoothJunction.coneMargin n m (ConicalJunctionPhysical.split x))
      (ConicalSmoothJunction.ballMargin a (ConicalJunctionPhysical.split x)) ≤
      (ConicalTipRounding.radius n)^2 := by
    unfold ConicalSmoothJunction.correction
    have ht := Real.smoothTransition.le_one
      (1 - ((ConicalSmoothJunction.coneMargin n m (ConicalJunctionPhysical.split x))^2 +
        (ConicalSmoothJunction.ballMargin a (ConicalJunctionPhysical.split x))^2) /
        (ConicalTipRounding.radius n)^2)
    nlinarith [sq_nonneg (ConicalTipRounding.radius n)]
  have hprod : 0 < (a/4 - ConicalTipRounding.radius n) * a^2 := mul_pos (by linarith) (sq_pos_of_pos ha)
  have hstrict : (ConicalTipRounding.radius n)^2 <
      2 * ConicalSmoothJunction.coneMargin n m (ConicalJunctionPhysical.split x) *
        ConicalSmoothJunction.ballMargin a (ConicalJunctionPhysical.split x) := by
    rw [hc, hb]
    nlinarith
  exact ⟨hcone, hball, hcorr.trans_lt hstrict⟩

/-- Every labelled upper and lower lobe is nonempty for one common sufficiently
    fine rounding index, for any finite family of positive radii. -/
theorem eventually_all_lobes_nonempty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → Data) (a : ι → ℝ) (center : ι → Space) (ha : ∀ i, 0 < a i) :
    ∀ᶠ n : ℕ in atTop, ∀ i : ι, ∀ up : Bool,
      (Packet07LobeGeometry.lobe p a center n i up).Nonempty := by
  have hr : Tendsto ConicalTipRounding.radius atTop (𝓝 0) := by
    simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hr2 : Tendsto (fun n => (ConicalTipRounding.radius n)^2) atTop (𝓝 0) := by
    simpa using hr.pow 2
  have he : ∀ᶠ n : ℕ in atTop, ∀ i : ι,
      ConicalTipRounding.radius n < a i / 4 ∧ (ConicalTipRounding.radius n)^2 < (a i)^3/4 := by
    apply Filter.eventually_all.mpr
    intro i
    have hai := ha i
    exact (hr.eventually (gt_mem_nhds (by positivity : 0 < a i / 4))).and
      (hr2.eventually (gt_mem_nhds (by positivity : 0 < (a i)^3/4)))
  filter_upwards [he] with n hn i up
  let z : ℝ := if up then a i / 2 else -(a i / 2)
  let x : Space := center i + EuclideanSpace.single 2 z
  have hz : |z| = a i / 2 := by
    cases up <;> simp [z, abs_of_pos (half_pos (ha i))]
  have hinc : x ∈ CommonBinaryInterface.component p a center n i := by
    change x - center i ∈ ConicalJunctionPhysical.inclusion n _ (a i)
    have heq : x - center i = EuclideanSpace.single 2 z := by simp [x]
    rw [heq]
    exact axial_point_inclusion n _ (a i) z (ha i) hz (hn i).1 (hn i).2
  refine ⟨x, hinc, ?_⟩
  cases up <;> simp [z, x, EuclideanSpace.single_apply, PiLp.add_apply, ha i]

end OQ14.Packet07LobeNonempty
#print axioms OQ14.Packet07LobeNonempty.axial_point_inclusion

#print axioms OQ14.Packet07LobeNonempty.eventually_all_lobes_nonempty
