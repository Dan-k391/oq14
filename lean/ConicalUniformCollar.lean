import ConicalPhysicalInterface

/-! Uniform exact coefficient agreement on compactly separated lateral collars. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalUniformCollar
open MeasureTheory Set Metric Filter OQ14.ConicalSmoothJunction OQ14.ConicalJunctionPhysical
open scoped Topology
abbrev Space := Maxwell.Space

def collar (δ b : ℝ) : Set Space := {x | δ ≤ ‖horizontal x‖ ∧ ‖x‖ ≤ b}

theorem lateral_interface_in_collar (t r b : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hr : 0 < r) (x : Space) (hx : r ≤ ‖x‖) (hb : ‖x‖ ≤ b)
    (hcone : t*‖x‖ = |x 2|) :
    x ∈ collar (r * Real.sqrt (1-t^2)) b := by
  have hp : 0 < 1-t^2 := by nlinarith
  have hs := Real.sq_sqrt hp.le
  have hsr := congrArg (fun v : ℝ => v*r^2) hs
  have hn := norm_sq_split x
  have hz : |x 2|^2 = (x 2)^2 := sq_abs _
  have he := congrArg (fun v : ℝ => v^2) hcone
  dsimp only at he hsr
  have hr2 := pow_le_pow_left₀ hr.le hx 2
  have hmul := mul_le_mul_of_nonneg_left hr2 hp.le
  have hδ : 0 ≤ r * Real.sqrt (1-t^2) := by positivity
  have hhs : 0 ≤ ‖horizontal x‖ := norm_nonneg _
  have hsq : (r * Real.sqrt (1-t^2))^2 ≤ ‖horizontal x‖^2 := by nlinarith
  exact ⟨by nlinarith, hb⟩

theorem ball_margin_lower (a b : ℝ) (hb : 0 ≤ b)
    (x : Space) (hx : ‖x‖ ≤ b) : a^2-b^2 ≤ ballMargin a (split x) := by
  have hnorm := norm_sq_split x
  have hn := norm_nonneg x
  dsimp [ballMargin, split]
  nlinarith [sq_nonneg (b-‖x‖)]

theorem eventually_collar_agreement (p : ConicalStaticVolume.Data) (a b δ : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hba : b < a) (hδ : 0 < δ)
    (hcut : a ≤ p.cutoff.rOut) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ collar δ b,
      (binaryMaterial p a n).value (VectorFourier.coordinateMap x) =
        (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap x) := by
  classical
  have hd : 0 < a^2-b^2 := by nlinarith
  have hr : Tendsto ConicalTipRounding.radius atTop (𝓝 0) := by
    simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
  have htwo : Tendsto (fun n => 2*ConicalTipRounding.radius n) atTop (𝓝 0) := by
    simpa using hr.const_mul 2
  have hsquare : Tendsto (fun n => (ConicalTipRounding.radius n)^2) atTop (𝓝 0) := by
    simpa using hr.pow 2
  have h1 := htwo.eventually (gt_mem_nhds hδ)
  have h2 := hsquare.eventually (gt_mem_nhds (sq_pos_of_pos hd))
  filter_upwards [h1,h2] with n hn1 hn2 x hx
  have hx1 : δ ≤ ‖horizontal x‖ := hx.1
  have hx2 : ‖x‖ ≤ b := hx.2
  have hball : a^2-b^2 ≤ ballMargin a (split x) := ball_margin_lower a b hb x hx2
  have hcorner : (ConicalTipRounding.radius n)^2 ≤
      (|(split x).2| - slope p.threshold * ‖(split x).1‖)^2 + (ballMargin a (split x))^2 := by
    have hs := pow_le_pow_left₀ hd.le hball 2
    nlinarith [sq_nonneg (|(split x).2| - slope p.threshold * ‖(split x).1‖)]
  have hm := ConicalSmoothJunction.inclusion_matches n (slope p.threshold) a
    (slope_properties p.threshold p.threshold_pos p.threshold_lt_one).1 (split x) (by dsimp [split]; linarith) hcorner
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz] at hx1
    have hzero : horizontal 0 = 0 := horizontalLinear.map_zero
    rw [hzero, norm_zero] at hx1
    linarith
  have hboundary : ‖x‖ ≠ a := ne_of_lt (lt_of_le_of_lt hx2 hba)
  have hball' : 0 < ballMargin a (split x) := lt_of_lt_of_le hd hball
  have hballnorm : ‖x‖ < a := lt_of_le_of_lt hx2 hba
  rw [original_binary p a hcut x hx0 hboundary]
  simp only [binaryMaterial, MeasurableEquiv.symm_apply_apply, ConicalJunctionPhysical.inclusion, mem_preimage]
  simp only [mem_inter_iff, mem_setOf_eq, hball', and_true] at hm
  rw [hm]
  simp only [hballnorm, and_true]

theorem norm_le_horizontal_add_axial (x : Space) : ‖x‖ ≤ ‖horizontal x‖ + |x 2| := by
  have hn := norm_sq_split x
  have hz : |x 2|^2 = (x 2)^2 := sq_abs _
  have hp : 0 ≤ ‖horizontal x‖*|x 2| := mul_nonneg (norm_nonneg _) (abs_nonneg _)
  nlinarith [norm_nonneg x, norm_nonneg (horizontal x), abs_nonneg (x 2)]

theorem eventually_annulus_agreement (p : ConicalStaticVolume.Data) (a b r : ℝ)
    (ha : 0 < a) (hr : 0 < r) (hba : b < a) (hcut : a ≤ p.cutoff.rOut) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Space, r ≤ ‖x‖ → ‖x‖ ≤ b →
      (binaryMaterial p a n).value (VectorFourier.coordinateMap x) =
        (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap x) := by
  classical
  let m := slope p.threshold
  let δ := r / (4*(m+1))
  have hm : 0 < m := (slope_properties p.threshold p.threshold_pos p.threshold_lt_one).1
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_cases hb : 0 ≤ b
  swap
  · filter_upwards with n x hxlo hxhi
    have hn := norm_nonneg x
    linarith
  have hd : 0 < a^2-b^2 := by nlinarith
  have heq : (m+1)*δ = r/4 := by dsimp [δ]; field_simp; ring
  have heps : Tendsto ConicalTipRounding.radius atTop (𝓝 0) := by
    simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hsquare : Tendsto (fun n => (ConicalTipRounding.radius n)^2) atTop (𝓝 0) := by simpa using heps.pow 2
  have hsmall := heps.eventually (gt_mem_nhds (show 0 < r/8 by positivity))
  have hcorner := hsquare.eventually (gt_mem_nhds (sq_pos_of_pos hd))
  have hlarge := eventually_collar_agreement p a b δ ha hb hba hδ hcut
  filter_upwards [hsmall,hcorner,hlarge] with n hn hn2 hnlarge x hxlo hxhi
  by_cases hδx : δ ≤ ‖horizontal x‖
  · exact hnlarge x ⟨hδx,hxhi⟩
  · have hsmallx : ‖horizontal x‖ < δ := lt_of_not_ge hδx
    have hnorm := norm_le_horizontal_add_axial x
    have hcap := ConicalJunctionRadial.cap_upper n m hm (horizontal x)
    have hmul := mul_lt_mul_of_pos_left hsmallx hm
    have hs : 0 < coneMargin n m (split x) := by
      dsimp [coneMargin, split]
      nlinarith
    have ht : 0 < ballMargin a (split x) := by
      have h := ball_margin_lower a b hb x hxhi
      linarith
    have hball := ball_margin_lower a b hb x hxhi
    have hcorner' : (ConicalTipRounding.radius n)^2 ≤
        (coneMargin n m (split x))^2 + (ballMargin a (split x))^2 := by
      have hs := pow_le_pow_left₀ hd.le hball 2
      nlinarith [sq_nonneg (coneMargin n m (split x))]
    have hzero := ConicalSmoothJunction.correction_zero n (coneMargin n m (split x)) (ballMargin a (split x)) hcorner'
    have hin : x ∈ ConicalJunctionPhysical.inclusion n m a := by
      change split x ∈ ConicalSmoothJunction.inclusion n m a
      exact ⟨hs, ht, by rw [hzero]; positivity⟩
    have horig := inclusion_material p a ha hcut n x hin
    simp [binaryMaterial, hin, horig, m]

end OQ14.ConicalUniformCollar
#print axioms OQ14.ConicalUniformCollar.eventually_collar_agreement
#print axioms OQ14.ConicalUniformCollar.lateral_interface_in_collar
#print axioms OQ14.ConicalUniformCollar.eventually_annulus_agreement
