import ConicalCommonEntire
import ConicalTipRounding
import MaterialVolumeLimit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.CommonTipRounding
open MeasureTheory Set Metric Filter OQ14.Maxwell
open scoped Topology
abbrev Space := Maxwell.Space
variable {ι : Type*} [Fintype ι]

def gate (center : ι → Space) (n : ℕ) (x : Space) : ℝ :=
  ∏ i : ι, ConicalTipRounding.gate n (x-center i)

theorem gate_bounds (center : ι → Space) (n : ℕ) (x : Space) : gate center n x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (ConicalTipRounding.gate_bounds n _).1)
  · apply Finset.prod_le_one
    · intro i _; exact (ConicalTipRounding.gate_bounds n _).1
    · intro i _; exact (ConicalTipRounding.gate_bounds n _).2

theorem gate_smooth (center : ι → Space) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (gate center n) := by
  unfold gate
  apply contDiff_prod
  intro i _
  exact (ConicalTipRounding.gate_smooth n).comp (contDiff_id.sub contDiff_const)

theorem gate_zero_inner (center : ι → Space) (n : ℕ) (i : ι) (x : Space)
    (hx : ‖x-center i‖ ≤ ConicalTipRounding.radius n) : gate center n x = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact ConicalTipRounding.gate_zero_inner n _ hx

theorem gate_eventually_one (center : ι → Space) (x : Space) (hx : ∀ i, x ≠ center i) :
    ∀ᶠ n : ℕ in atTop, gate center n x=1 := by
  have h : ∀ᶠ n : ℕ in atTop, ∀ i, ConicalTipRounding.gate n (x-center i)=1 :=
    Filter.eventually_all.mpr (fun i => ConicalTipRounding.gate_eventually_one _ (sub_ne_zero.mpr (hx i)))
  filter_upwards [h] with n hn
  simp [gate,hn]

def rounded (center : ι → Space) (c : StaticCoefficient.Coefficient) (n : ℕ) : StaticCoefficient.Coefficient where
  value ξ := gate center n (VectorFourier.coordinateMap.symm ξ)*c.value ξ
  bound := c.bound
  measurable := (((gate_smooth center n).continuous.measurable.comp VectorFourier.coordinateMap.symm.measurable).mul c.measurable)
  nonnegative ξ := mul_nonneg (gate_bounds center n _).1 (c.nonnegative ξ)
  bounded ξ := (mul_le_of_le_one_left (c.nonnegative ξ) (gate_bounds center n _).2).trans (c.bounded ξ)

theorem rounded_spatial (center : ι → Space) (c : StaticCoefficient.Coefficient) (n : ℕ) (x : Space) :
    (rounded center c n).value (VectorFourier.coordinateMap x)=gate center n x*c.value (VectorFourier.coordinateMap x) := by
  simp [rounded]

theorem rounded_zero_inner (center : ι → Space) (c : StaticCoefficient.Coefficient) (n : ℕ) (i : ι) (x : Space)
    (hx : ‖x-center i‖ ≤ ConicalTipRounding.radius n) :
    (rounded center c n).value (VectorFourier.coordinateMap x)=0 := by
  rw [rounded_spatial,gate_zero_inner center n i x hx,zero_mul]

theorem rounded_tendsto (center : ι → Space) (c : StaticCoefficient.Coefficient) :
    ∀ᵐ ξ : StaticCoefficient.Space, Tendsto (fun n => (rounded center c n).value ξ) atTop (𝓝 (c.value ξ)) := by
  have he : ∀ᵐ ξ : StaticCoefficient.Space, ∀ i, ξ ≠ VectorFourier.coordinateMap (center i) := by
    apply ae_all_iff.mpr
    intro i
    exact (countable_singleton _).ae_not_mem volume
  filter_upwards [he] with ξ hξ
  have hx : ∀ i, VectorFourier.coordinateMap.symm ξ ≠ center i := by
    intro i h
    apply hξ i
    rw [← h,MeasurableEquiv.apply_symm_apply]
  have hg := gate_eventually_one center _ hx
  apply tendsto_const_nhds.congr'
  exact hg.mono (fun n hn => by simp [rounded,hn])

theorem volumeField_tendsto (center : ι → Space) (c : StaticCoefficient.Coefficient)
    (k R : ℝ) (hR : 0 ≤ R) (hk : |k| ≤ MaterialVolumeLimit.commonRadius c.bound R)
    (incident : VectorFourier.VectorL2) :
    Tendsto (fun n => MaterialVolumeLimit.volumeField (rounded center c n) k R incident) atTop
      (𝓝 (MaterialVolumeLimit.volumeField c k R incident)) :=
  MaterialVolumeLimit.volumeField_tendsto (rounded center c) c c.bound k R hR (fun _ => le_rfl) le_rfl
    (rounded_tendsto center c) hk incident
theorem rounded_support (center : ι → Space) (c : StaticCoefficient.Coefficient) (n : ℕ) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x)=0)
    (x : Space) (hx : x ∉ closedBall (0 : Space) R) :
    (rounded center c n).value (VectorFourier.coordinateMap x)=0 := by
  rw [rounded_spatial, hc x hx, mul_zero]

theorem rounded_smooth_near_tip (center : ι → Space) (c : StaticCoefficient.Coefficient) (n : ℕ) (i : ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Space => (rounded center c n).value (VectorFourier.coordinateMap x))
      (ball (center i) (ConicalTipRounding.radius n)) := by
  apply contDiffOn_const.congr
  intro x hx
  have hn : ‖x-center i‖ < ConicalTipRounding.radius n := by simpa [mem_ball,dist_eq_norm] using hx
  exact rounded_zero_inner center c n i x hn.le
end OQ14.CommonTipRounding
#print axioms OQ14.CommonTipRounding.gate_bounds
#print axioms OQ14.CommonTipRounding.gate_smooth
#print axioms OQ14.CommonTipRounding.gate_zero_inner
#print axioms OQ14.CommonTipRounding.gate_eventually_one
#print axioms OQ14.CommonTipRounding.rounded_zero_inner
#print axioms OQ14.CommonTipRounding.rounded_tendsto
#print axioms OQ14.CommonTipRounding.volumeField_tendsto


#print axioms OQ14.CommonTipRounding.rounded_support
#print axioms OQ14.CommonTipRounding.rounded_smooth_near_tip

