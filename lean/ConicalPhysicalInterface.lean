import ConicalJunctionPhysical
import ConicalJunctionInterface

/-! Transfer the regular-level-set certificate to physical three-dimensional space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalPhysicalInterface
open Set Filter OQ14.ConicalSmoothJunction OQ14.ConicalJunctionPhysical
open scoped Topology
abbrev Space := Maxwell.Space

def join (x : Point) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x.1 0, x.1 1, x.2]

def splitEquiv : Space ≃ₗ[ℝ] Point where
  toFun := split
  invFun := join
  left_inv x := by
    ext i
    fin_cases i <;> simp [split, join, horizontal]
  right_inv x := by
    apply Prod.ext
    · ext i
      fin_cases i <;> simp [split, join, horizontal]
    · simp [split, join]
  map_add' x y := by
    apply Prod.ext
    · exact horizontalLinear.map_add x y
    · simp [split]
  map_smul' c x := by
    apply Prod.ext
    · exact horizontalLinear.map_smul c x
    · simp [split]

def splitHomeomorph : Space ≃ₜ Point := splitEquiv.toContinuousLinearEquiv.toHomeomorph

theorem split_frontier (n : ℕ) (m a : ℝ) (x : Space)
    (hx : x ∈ frontier (ConicalJunctionPhysical.inclusion n m a)) :
    split x ∈ frontier (ConicalSmoothJunction.inclusion n m a) := by
  have h := splitHomeomorph.image_frontier (ConicalJunctionPhysical.inclusion n m a)
  have hx' : splitHomeomorph x ∈ splitHomeomorph '' frontier (ConicalJunctionPhysical.inclusion n m a) := ⟨x,hx,rfl⟩
  rw [h] at hx'
  have he : split '' (split ⁻¹' ConicalSmoothJunction.inclusion n m a) = ConicalSmoothJunction.inclusion n m a :=
    Set.image_preimage_eq _ splitEquiv.surjective
  change split x ∈ frontier (split '' (split ⁻¹' ConicalSmoothJunction.inclusion n m a)) at hx'
  rwa [he] at hx'

def physicalDef (n : ℕ) (m a : ℝ) (x : Space) : ℝ := defining n m a (split x)

theorem physical_local_certificate (n : ℕ) (m a : ℝ) (hm : 0 < m) (x : Space)
    (hx : x ∈ frontier (ConicalJunctionPhysical.inclusion n m a))
    (ha : (4 + (2*m+2)^2) * (ConicalTipRounding.radius n)^2 +
      ConicalTipRounding.radius n < a^2) :
    ContDiffAt ℝ (⊤ : ℕ∞) (physicalDef n m a) x ∧ physicalDef n m a x = 0 ∧
      fderiv ℝ (physicalDef n m a) x ≠ 0 ∧
      ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
        (y ∈ ConicalJunctionPhysical.inclusion n m a ↔ 0 < physicalDef n m a y) := by
  have hf := split_frontier n m a x hx
  have hz := ConicalJunctionInterface.frontier_nonzero_axial n m a hm (split x) hf
  have hsm := ConicalSmoothJunction.defining_smooth_at n m a hm (split x) hz
  have hnonzero := ConicalJunctionInterface.frontier_fderiv_nonzero n m a hm (split x) hf ha
  have hsplit : ContDiff ℝ (⊤ : ℕ∞) split := splitEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  refine ⟨hsm.comp x hsplit.contDiffAt, (ConicalJunctionInterface.frontier_margins n m a hm (split x) hf).2.2, ?_, ?_⟩
  · intro hzero
    have hd := (hsm.differentiableAt (by norm_num)).hasFDerivAt
    have hmap : HasFDerivAt split splitEquiv.toContinuousLinearEquiv.toContinuousLinearMap x :=
      splitEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt
    have hcomp := hd.comp x hmap
    have heq : fderiv ℝ (physicalDef n m a) x =
        (fderiv ℝ (defining n m a) (split x)).comp splitEquiv.toContinuousLinearEquiv.toContinuousLinearMap := hcomp.fderiv
    apply hnonzero
    apply ContinuousLinearMap.ext
    intro y
    obtain ⟨v, rfl⟩ := splitEquiv.surjective y
    have hv := congrArg (fun f : Space →L[ℝ] ℝ => f v) hzero
    rw [heq] at hv
    simpa using hv
  · obtain ⟨V,hV,hxV,hlevel⟩ := ConicalJunctionInterface.frontier_local_level n m a hm (split x) hf
    refine ⟨split ⁻¹' V, hV.preimage split_continuous, hxV, ?_⟩
    intro y hy
    exact hlevel (split y) hy

theorem eventually_smooth_boundary (m a : ℝ) (hm : 0 < m) (ha : a ≠ 0) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ frontier (ConicalJunctionPhysical.inclusion n m a),
      ContDiffAt ℝ (⊤ : ℕ∞) (physicalDef n m a) x ∧ physicalDef n m a x = 0 ∧
        fderiv ℝ (physicalDef n m a) x ≠ 0 ∧
        ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
          (y ∈ ConicalJunctionPhysical.inclusion n m a ↔ 0 < physicalDef n m a y) := by
  filter_upwards [ConicalJunctionRadial.eventually_separated m a ha] with n hn x hx
  exact physical_local_certificate n m a hm x hx hn

theorem eventually_local_sharp (m a : ℝ) (hm : 0 < m) (x : Space)
    (hh : horizontal x ≠ 0) (hb : 0 < ballMargin a (split x)) :
    ∀ᶠ n : ℕ in atTop, ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U,
      (y ∈ ConicalJunctionPhysical.inclusion n m a ↔
        split y ∈ ConicalSmoothCapGraph.sharpCone m ∧ 0 < ballMargin a (split y)) := by
  have hr : Tendsto ConicalTipRounding.radius atTop (𝓝 0) := by
    simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
  have htwo : Tendsto (fun n => 2*ConicalTipRounding.radius n) atTop (𝓝 0) := by
    simpa using hr.const_mul 2
  have hsquare : Tendsto (fun n => (ConicalTipRounding.radius n)^2) atTop (𝓝 0) := by
    simpa using hr.pow 2
  have h1 := htwo.eventually (gt_mem_nhds (norm_pos_iff.mpr hh))
  have h2 := hsquare.eventually (gt_mem_nhds (sq_pos_of_pos hb))
  filter_upwards [h1,h2] with n hn1 hn2
  let U : Set Space := {y | 2*ConicalTipRounding.radius n < ‖horizontal y‖ ∧
    (ConicalTipRounding.radius n)^2 < (ballMargin a (split y))^2}
  have hc1 : Continuous (fun y : Space => ‖horizontal y‖) := continuous_norm.comp horizontalLinear.continuous_of_finiteDimensional
  have hc2 : Continuous (fun y : Space => (ballMargin a (split y))^2) := by
    have hc : Continuous (ballMargin a) :=
      (continuous_const.sub ((continuous_norm.comp continuous_fst).pow 2)).sub (continuous_snd.pow 2)
    exact (hc.comp split_continuous).pow 2
  refine ⟨U, (isOpen_lt continuous_const hc1).inter (isOpen_lt continuous_const hc2), ⟨hn1,hn2⟩, ?_⟩
  intro y hy
  change 2*ConicalTipRounding.radius n < ‖horizontal y‖ ∧
    (ConicalTipRounding.radius n)^2 < (ballMargin a (split y))^2 at hy
  have hcorner : (ConicalTipRounding.radius n)^2 ≤
      (|(split y).2| - m*‖(split y).1‖)^2 + (ballMargin a (split y))^2 := by
    nlinarith [sq_nonneg (|(split y).2| - m*‖(split y).1‖)]
  exact ConicalSmoothJunction.inclusion_matches n m a hm (split y) hy.1.le hcorner

end OQ14.ConicalPhysicalInterface
#print axioms OQ14.ConicalPhysicalInterface.split_frontier
#print axioms OQ14.ConicalPhysicalInterface.physical_local_certificate
#print axioms OQ14.ConicalPhysicalInterface.eventually_smooth_boundary
#print axioms OQ14.ConicalPhysicalInterface.eventually_local_sharp
