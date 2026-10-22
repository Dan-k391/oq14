import RadialGluing
import RadialElectricCurl

/-! Explicit finite layer coefficients, clipped only near the excluded source point. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ClippedLayerProfiles
open MeasureTheory Set Filter OQ14.Maxwell OQ14.RadialStack OQ14.RadialGluing
open scoped Topology

def select (gs : List Layer) (f : Layer → ℝ → ℂ) (d : ℝ → ℂ) (r : ℝ) : ℂ :=
  match gs with
  | [] => d r
  | g::gs => if g.a < r then f g r else select gs f d r

theorem select_measurable (gs : List Layer) (f : Layer → ℝ → ℂ) (d : ℝ → ℂ)
    (hf : ∀ g, Measurable (f g)) (hd : Measurable d) : Measurable (select gs f d) := by
  induction gs with
  | nil => exact hd
  | cons g gs ih =>
    exact (hf g).ite (measurableSet_lt measurable_const measurable_id) ih

theorem select_continuousAt (gs : List Layer) (f : Layer → ℝ → ℂ) (d : ℝ → ℂ)
    (r : ℝ) (hr : r ∉ cuts gs) (hf : ∀ g, ContinuousAt (f g) r)
    (hd : ContinuousAt d r) : ContinuousAt (select gs f d) r := by
  induction gs with
  | nil => exact hd
  | cons g gs ih =>
    have hn : r ≠ g.a := by intro he; exact hr (by simp [cuts,he])
    have ht : r ∉ cuts gs := fun h => hr (List.mem_cons_of_mem _ h)
    rcases lt_or_gt_of_ne hn with hlt|hgt
    · apply (ih ht).congr
      filter_upwards [Iio_mem_nhds hlt] with t h
      exact (if_neg (not_lt.mpr h.le)).symm
    · apply (hf g).congr
      filter_upwards [Ioi_mem_nhds hgt] with t h
      exact (if_pos h).symm

private theorem locallyIntegrable_ite {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) (s : Set X) [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (f g : X → ℂ) (hf : LocallyIntegrable f μ)
    (hg : LocallyIntegrable g μ) : LocallyIntegrable (s.piecewise f g) μ := by
  have he : s.piecewise f g=s.indicator f+sᶜ.indicator g := by
    ext x
    by_cases hx : x ∈ s <;> simp [Set.piecewise,Set.indicator,hx]
  rw [he]
  exact (hf.indicator hs).add (hg.indicator hs.compl)

theorem select_comp_locallyIntegrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (gs : List Layer) (f : Layer → ℝ → ℂ) (d : ℝ → ℂ)
    (ρ : X → ℝ) (hρ : Measurable ρ)
    (hf : ∀ g, LocallyIntegrable (fun x => f g (ρ x)) μ)
    (hd : LocallyIntegrable (fun x => d (ρ x)) μ) :
    LocallyIntegrable (fun x => select gs f d (ρ x)) μ := by
  induction gs with
  | nil => exact hd
  | cons g gs ih =>
    exact locallyIntegrable_ite μ {x | g.a < ρ x}
      (measurableSet_lt measurable_const hρ) _ _ (hf g) ih

def radius (c r : ℝ) : ℝ := max c r

theorem radius_continuous (c : ℝ) : Continuous (radius c) := continuous_const.max continuous_id

theorem radius_pos (c r : ℝ) (hc : 0 < c) : 0 < radius c r := hc.trans_le (le_max_left _ _)

def state (l : ℕ) (gs : List Layer) (s : State) (c r : ℝ) : State :=
  profile l gs s (radius c r)

theorem state_continuous (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (c : ℝ) : Continuous (state l gs s c) :=
  (profile_continuous l h s).comp (radius_continuous c)

def inverseSigma (gs : List Layer) (r : ℝ) : ℂ :=
  select gs (fun g _ => (g.σ : ℂ)⁻¹) (fun _ => 0) r

def potential (l : ℕ) (gs : List Layer) (r : ℝ) : ℂ :=
  select gs (fun g t => (RadialLayer.potential l g.q g.σ t : ℂ)) (fun _ => 0) r

theorem potential_eq (l : ℕ) (gs : List Layer) (r : ℝ) :
    potential l gs r=(potentialAt l gs r : ℂ) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    unfold potential select potentialAt
    split_ifs <;> simp_all [potential]

theorem inverseSigma_measurable (gs : List Layer) : Measurable (inverseSigma gs) :=
  select_measurable gs _ _ (fun _ => measurable_const) measurable_const

theorem potential_measurable (l : ℕ) (gs : List Layer) : Measurable (potential l gs) := by
  apply select_measurable
  · intro g
    unfold RadialLayer.potential
    fun_prop
  · exact measurable_const

theorem inverseSigma_continuousAt (gs : List Layer) (r : ℝ) (hr : r ∉ cuts gs) :
    ContinuousAt (inverseSigma gs) r :=
  select_continuousAt gs _ _ r hr (fun _ => continuousAt_const) continuousAt_const

theorem potential_continuousAt (l : ℕ) (gs : List Layer) (r : ℝ)
    (hr : r ∉ cuts gs) (hr0 : r ≠ 0) : ContinuousAt (potential l gs) r := by
  apply select_continuousAt gs _ _ r hr
  · intro g
    unfold RadialLayer.potential
    exact Complex.continuous_ofReal.continuousAt.comp
      ((continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 2))
        (mul_ne_zero g.σ_pos.ne' (pow_ne_zero 2 hr0))).sub continuousAt_const)
  · exact continuousAt_const

theorem inverseSigma_comp_locallyIntegrable (gs : List Layer) (ρ : Space → ℝ)
    (hρ : Continuous ρ) : LocallyIntegrable (fun x => inverseSigma gs (ρ x)) :=
  select_comp_locallyIntegrable volume gs _ _ ρ hρ.measurable
    (fun _ => continuous_const.locallyIntegrable) continuous_const.locallyIntegrable

theorem potential_clipped_continuous_branch (l : ℕ) (g : Layer) (c : ℝ) (hc : 0 < c) :
    Continuous (fun r => (RadialLayer.potential l g.q g.σ (radius c r) : ℂ)) := by
  apply Complex.continuous_ofReal.comp
  exact (continuous_const.div (continuous_const.mul ((radius_continuous c).pow 2))
    (fun r => mul_ne_zero g.σ_pos.ne' (pow_ne_zero 2 (radius_pos c r hc).ne'))).sub continuous_const

theorem potential_comp_locallyIntegrable (l : ℕ) (gs : List Layer) (c : ℝ) (hc : 0 < c)
    (ρ : Space → ℝ) (hρ : Continuous ρ) :
    LocallyIntegrable (fun x => potential l gs (radius c (ρ x))) := by
  apply select_comp_locallyIntegrable volume gs _ _ _ ((radius_continuous c).comp hρ).measurable
  · intro g
    exact ((potential_clipped_continuous_branch l g c hc).comp hρ).locallyIntegrable
  · exact continuous_const.locallyIntegrable

end OQ14.ClippedLayerProfiles

#print axioms OQ14.ClippedLayerProfiles.select_measurable
#print axioms OQ14.ClippedLayerProfiles.select_continuousAt
#print axioms OQ14.ClippedLayerProfiles.select_comp_locallyIntegrable
#print axioms OQ14.ClippedLayerProfiles.radius_continuous
#print axioms OQ14.ClippedLayerProfiles.radius_pos
#print axioms OQ14.ClippedLayerProfiles.state_continuous
#print axioms OQ14.ClippedLayerProfiles.potential_eq
#print axioms OQ14.ClippedLayerProfiles.inverseSigma_measurable
#print axioms OQ14.ClippedLayerProfiles.potential_measurable
#print axioms OQ14.ClippedLayerProfiles.inverseSigma_continuousAt
#print axioms OQ14.ClippedLayerProfiles.potential_continuousAt
#print axioms OQ14.ClippedLayerProfiles.inverseSigma_comp_locallyIntegrable
#print axioms OQ14.ClippedLayerProfiles.potential_clipped_continuous_branch
#print axioms OQ14.ClippedLayerProfiles.potential_comp_locallyIntegrable
