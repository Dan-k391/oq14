import MaterialCellGraph
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Actual concentric material cells and interface bridges

The cells are literal Euclidean balls, annuli and exteriors. Their connectivity
comes from actual rank-three sphere connectivity and the continuous radial
image. Interface spheres have actual zero volume, and explicit small balls
cross each radial interface.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.RadialMaterialCells

open MeasureTheory Metric Set OQ14.Maxwell OQ14.MaterialCellGraph
open scoped Topology

def inner (r : ℝ) : Set Space := ball 0 r
def annulus (a b : ℝ) : Set Space := {x | a < ‖x‖ ∧ ‖x‖ < b}
def exterior (r : ℝ) : Set Space := {x | r < ‖x‖}

theorem rank_three : Module.rank ℝ Space = 3 := by
  rw [← Module.finrank_eq_rank]
  simp [Space]

theorem radial_image (s : Set ℝ) (hs : ∀ r ∈ s, 0 < r) :
    (fun p : Space × ℝ => p.2 • p.1) '' (sphere (0 : Space) 1 ×ˢ s) = {x | ‖x‖ ∈ s} := by
  apply Subset.antisymm
  · rintro x ⟨⟨n,r⟩,⟨hn,hr⟩,rfl⟩
    have hn' : ‖n‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hn
    simpa only [mem_setOf_eq,norm_smul,Real.norm_eq_abs,abs_of_pos (hs r hr),hn',mul_one] using hr
  · intro x hx
    have hp : 0 < ‖x‖ := hs ‖x‖ hx
    refine ⟨(‖x‖⁻¹ • x,‖x‖),⟨?_,hx⟩,?_⟩
    · simp only [mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (ne_of_gt hp)]
    · simp only [smul_smul,mul_inv_cancel₀ (ne_of_gt hp),one_smul]

theorem radial_preconnected (s : Set ℝ) (hs : ∀ r ∈ s, 0 < r) (hc : IsPreconnected s) :
    IsPreconnected {x : Space | ‖x‖ ∈ s} := by
  have hS : IsPreconnected (sphere (0 : Space) 1) :=
    isPreconnected_sphere (by rw [rank_three]; norm_num) 0 1
  rw [← radial_image s hs]
  exact (hS.prod hc).image _ (continuous_snd.smul continuous_fst).continuousOn

theorem inner_open (r : ℝ) : IsOpen (inner r) := isOpen_ball
theorem annulus_open (a b : ℝ) : IsOpen (annulus a b) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
theorem exterior_open (r : ℝ) : IsOpen (exterior r) := isOpen_lt continuous_const continuous_norm

theorem inner_preconnected (r : ℝ) : IsPreconnected (inner r) :=
  (convex_ball (0 : Space) r).isPreconnected

theorem annulus_preconnected (a b : ℝ) (ha : 0 ≤ a) : IsPreconnected (annulus a b) :=
  radial_preconnected (Ioo a b) (fun _ hr => lt_of_le_of_lt ha hr.1) (convex_Ioo a b).isPreconnected

theorem exterior_preconnected (r : ℝ) (hr : 0 ≤ r) : IsPreconnected (exterior r) :=
  radial_preconnected (Ioi r) (fun _ hs => lt_of_le_of_lt hr hs) (convex_Ioi r).isPreconnected

theorem ae_norm_ne (r : ℝ) : ∀ᵐ x : Space, ‖x‖ ≠ r := by
  have hs : (volume : Measure Space) (sphere 0 r) = 0 := Measure.addHaar_sphere volume 0 r
  simpa only [ae_iff,ne_eq,not_not,sphere,dist_zero_right] using hs

theorem bridge_mono {U V U' V' : Set Space} (h : Bridge U V)
    (hU : U ⊆ U') (hV : V ⊆ V') : Bridge U' V' := by
  obtain ⟨B,hB,hBc,hcov,hBU,hBV⟩ := h
  refine ⟨B,hB,hBc,?_,?_,?_⟩
  · filter_upwards [hcov] with x hx hb
    exact (hx hb).imp (fun h => hU h) (fun h => hV h)
  · obtain ⟨x,hx,hxU⟩ := hBU
    exact ⟨x,hx,hU hxU⟩
  · obtain ⟨x,hx,hxV⟩ := hBV
    exact ⟨x,hx,hV hxV⟩

def axis (r : ℝ) : Space := r • basis 0

theorem axis_norm (r : ℝ) : ‖axis r‖ = |r| := by
  simp only [axis,norm_smul,Real.norm_eq_abs,basis,EuclideanSpace.norm_single,norm_one,mul_one]

theorem axis_dist (r s : ℝ) : dist (axis r) (axis s) = |r-s| := by
  change ‖r • basis 0-s • basis 0‖ = _
  rw [← sub_smul]
  exact axis_norm (r-s)

theorem annulus_bridge_of_radius (a r b δ : ℝ) (ha : 0 ≤ a)
    (har : a < r) (_hrb : r < b) (hδ : 0 < δ) (hδa : δ < r-a) (hδb : δ < b-r) :
    Bridge (annulus a r) (annulus r b) := by
  have hr : 0 < r := lt_of_le_of_lt ha har
  have hn : ‖axis r‖ = r := by rw [axis_norm,abs_of_pos hr]
  have hbounds (x : Space) (hx : x ∈ ball (axis r) δ) : a < ‖x‖ ∧ ‖x‖ < b := by
    have hd : ‖x-axis r‖ < δ := by simpa only [mem_ball,dist_eq_norm] using hx
    have hu := norm_add_le (x-axis r) (axis r)
    rw [sub_add_cancel,hn] at hu
    have hl := norm_add_le (axis r-x) x
    rw [sub_add_cancel,hn,norm_sub_rev] at hl
    constructor <;> linarith
  refine ⟨ball (axis r) δ,isOpen_ball,isConnected_ball hδ,?_,?_,?_⟩
  · filter_upwards [ae_norm_ne r] with x hx hb
    obtain ⟨hlo,hhi⟩ := hbounds x hb
    rcases lt_or_gt_of_ne hx with hl | hr
    · exact Or.inl ⟨hlo,hl⟩
    · exact Or.inr ⟨hr,hhi⟩
  · refine ⟨axis (r-δ/2),?_,?_⟩
    · rw [mem_ball,axis_dist]
      rw [show r-δ/2-r = -(δ/2) by ring,abs_neg,abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    · change a < ‖axis (r-δ/2)‖ ∧ ‖axis (r-δ/2)‖ < r
      rw [axis_norm,abs_of_pos (by linarith : 0 < r-δ/2)]
      constructor <;> linarith
  · refine ⟨axis (r+δ/2),?_,?_⟩
    · rw [mem_ball,axis_dist]
      rw [show r+δ/2-r = δ/2 by ring,abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    · change r < ‖axis (r+δ/2)‖ ∧ ‖axis (r+δ/2)‖ < b
      rw [axis_norm,abs_of_pos (by linarith : 0 < r+δ/2)]
      constructor <;> linarith

theorem annulus_bridge (a r b : ℝ) (ha : 0 ≤ a) (har : a < r) (hrb : r < b) :
    Bridge (annulus a r) (annulus r b) := by
  have hm : 0 < min (r-a) (b-r) := lt_min (sub_pos.mpr har) (sub_pos.mpr hrb)
  exact annulus_bridge_of_radius a r b (min (r-a) (b-r)/2) ha har hrb (half_pos hm)
    ((half_lt_self hm).trans_le (min_le_left _ _))
    ((half_lt_self hm).trans_le (min_le_right _ _))

theorem inner_annulus_bridge (r b : ℝ) (hr : 0 < r) (hb : r < b) :
    Bridge (inner r) (annulus r b) := by
  apply bridge_mono (annulus_bridge 0 r b le_rfl hr hb) _ (Subset.refl _)
  intro x hx
  exact (mem_ball_zero_iff).mpr hx.2

theorem annulus_exterior_bridge (a r : ℝ) (ha : 0 ≤ a) (hr : a < r) :
    Bridge (annulus a r) (exterior r) := by
  apply bridge_mono (annulus_bridge a r (r+1) ha hr (by linarith)) (Subset.refl _) _
  exact fun _ hx => hx.1

theorem inner_exterior_bridge (r : ℝ) (hr : 0 < r) : Bridge (inner r) (exterior r) := by
  apply bridge_mono (inner_annulus_bridge r (r+1) hr (by linarith)) (Subset.refl _) _
  exact fun _ hx => hx.1

end OQ14.RadialMaterialCells

#print axioms OQ14.RadialMaterialCells.rank_three
#print axioms OQ14.RadialMaterialCells.radial_image
#print axioms OQ14.RadialMaterialCells.radial_preconnected
#print axioms OQ14.RadialMaterialCells.inner_open
#print axioms OQ14.RadialMaterialCells.annulus_open
#print axioms OQ14.RadialMaterialCells.exterior_open
#print axioms OQ14.RadialMaterialCells.inner_preconnected
#print axioms OQ14.RadialMaterialCells.annulus_preconnected
#print axioms OQ14.RadialMaterialCells.exterior_preconnected
#print axioms OQ14.RadialMaterialCells.ae_norm_ne
#print axioms OQ14.RadialMaterialCells.bridge_mono
#print axioms OQ14.RadialMaterialCells.axis_norm
#print axioms OQ14.RadialMaterialCells.axis_dist
#print axioms OQ14.RadialMaterialCells.annulus_bridge_of_radius
#print axioms OQ14.RadialMaterialCells.annulus_bridge
#print axioms OQ14.RadialMaterialCells.inner_annulus_bridge
#print axioms OQ14.RadialMaterialCells.annulus_exterior_bridge
#print axioms OQ14.RadialMaterialCells.inner_exterior_bridge
