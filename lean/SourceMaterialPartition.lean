import SourceMaterialCoefficient
import FiniteRadialPartition
import Mathlib.Data.Finset.Sort

/-! Actual radial cells for every finite source stack, with repeated cuts removed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OQ14.SourceMaterialPartition
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem
open OQ14.SourceMaterialCoefficient
attribute [local instance] Classical.propDecidable

def cutSet (d : Data) : Finset ℝ := insert d.R (insert d.X (RadialGluing.cuts d.gs).toFinset)
def degree (d : Data) : ℕ := (cutSet d).card-1

theorem card_eq (d : Data) : (cutSet d).card=degree d+1 := by
  have hp : 0<(cutSet d).card := Finset.card_pos.mpr ⟨d.R,by simp [cutSet]⟩
  unfold degree
  omega

def radii (d : Data) : Fin (degree d+1) → ℝ := (cutSet d).orderEmbOfFin (card_eq d)

theorem radii_strictMono (d : Data) : StrictMono (radii d) :=
  ((cutSet d).orderEmbOfFin (card_eq d)).strictMono

theorem radii_positive (d : Data) (i : Fin (degree d+1)) : 0<radii d i := by
  have hi := (cutSet d).orderEmbOfFin_mem (card_eq d) i
  change radii d i∈cutSet d at hi
  simp only [cutSet,Finset.mem_insert,List.mem_toFinset] at hi
  rcases hi with h|h|h
  · exact h ▸ d.hR
  · exact h ▸ d.hR.trans_le (RadialStack.chain_ordered d.chain)
  · obtain ⟨g,hg,he⟩ := List.mem_map.mp h
    rw [←he]
    exact g.a_pos

theorem exists_radius (d : Data) {a : ℝ} (ha : a∈cutSet d) :
    ∃ i, radii d i=a := by
  let i := ((cutSet d).orderIsoOfFin (card_eq d)).symm ⟨a,ha⟩
  refine ⟨i,?_⟩
  exact congrArg Subtype.val (((cutSet d).orderIsoOfFin (card_eq d)).apply_symm_apply ⟨a,ha⟩)

theorem cell_comparisons {n : ℕ} (r : Fin (n+1) → ℝ) (j : Fin (n+2))
    {x y : Space} (hx : x∈FiniteRadialPartition.cell r j)
    (hy : y∈FiniteRadialPartition.cell r j) (i : Fin (n+1)) :
    (r i<‖x‖ ↔ r i<‖y‖) ∧ (‖x‖≤r i ↔ ‖y‖≤r i) := by
  by_cases hi : i.val<j.val
  · exact ⟨iff_of_true (hx.1 i hi) (hy.1 i hi),
      iff_of_false (not_le.mpr (hx.1 i hi)) (not_le.mpr (hy.1 i hi))⟩
  · have hi' : j.val ≤ i.val := le_of_not_gt hi
    exact ⟨iff_of_false (not_lt.mpr (hx.2 i hi').le) (not_lt.mpr (hy.2 i hi').le),
      iff_of_true (hx.2 i hi').le (hy.2 i hi').le⟩

theorem sigmaAt_eq_of_comparisons (gs : List RadialStack.Layer) (s t : ℝ)
    (h : ∀ g∈gs, g.a<s ↔ g.a<t) : RadialGluing.sigmaAt gs s=RadialGluing.sigmaAt gs t := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := h g (by simp)
    by_cases hs : g.a<s
    · simp only [RadialGluing.sigmaAt,if_pos hs,if_pos (hg.mp hs)]
    · simp only [RadialGluing.sigmaAt,if_neg hs,if_neg (fun ht => hs (hg.mpr ht))]
      exact ih (fun a ha => h a (by simp [ha]))

theorem realSigma_cell (d : Data) (j : Fin (degree d+2)) {x y : Space}
    (hx : x∈FiniteRadialPartition.cell (radii d) j)
    (hy : y∈FiniteRadialPartition.cell (radii d) j) : realSigma d ‖x‖=realSigma d ‖y‖ := by
  have hc (a : ℝ) (ha : a∈cutSet d) :
      (a<‖x‖ ↔ a<‖y‖) ∧ (‖x‖≤a ↔ ‖y‖≤a) := by
    obtain ⟨i,rfl⟩ := exists_radius d ha
    exact cell_comparisons (radii d) j hx hy i
  have hR := (hc d.R (by simp [cutSet])).2
  have hX := (hc d.X (by simp [cutSet])).2
  unfold realSigma
  by_cases hr : ‖x‖≤d.R
  · simp only [if_pos hr,if_pos (hR.mp hr)]
  · simp only [if_neg hr,if_neg (fun ht => hr (hR.mpr ht))]
    by_cases hs : ‖x‖≤d.X
    · simp only [if_pos hs,if_pos (hX.mp hs)]
      apply sigmaAt_eq_of_comparisons
      intro g hg
      exact (hc g.a (by simp [cutSet,RadialGluing.cuts,List.mem_map.mpr ⟨g,hg,rfl⟩])).1
    · simp only [if_neg hs,if_neg (fun ht => hs (hX.mpr ht))]

def cellValue (d : Data) (j : Fin (degree d+2)) : ℝ :=
  if h : (FiniteRadialPartition.cell (radii d) j).Nonempty then realSigma d ‖h.choose‖ else 1

theorem cellValue_positive (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M) (j : Fin (degree d+2)) : 0<cellValue d j := by
  unfold cellValue
  split_ifs
  · exact lt_of_lt_of_le zero_lt_one (realSigma_bounds d M hM hs _).1
  · exact zero_lt_one

theorem dielectric_cell (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M) (j : Fin (degree d+2)) (x : Space)
    (hx : x∈FiniteRadialPartition.cell (radii d) j) :
    MaterialMaxwell.dielectric (coefficient d M hM hs) x=cellValue d j := by
  rw [dielectric_eq]
  have hn : (FiniteRadialPartition.cell (radii d) j).Nonempty := ⟨x,hx⟩
  rw [cellValue,dif_pos hn]
  exact realSigma_cell d j hx hn.choose_spec

def partition (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M) :
    PiecewiseMaxwellUniqueness.Partition (Fin (degree d+2))
      (MaterialMaxwell.dielectric (coefficient d M hM hs)) :=
  FiniteRadialPartition.partition (radii d) (radii_strictMono d) (radii_positive d) _
    (cellValue d) (cellValue_positive d M hM hs)
    (fun j => Filter.Eventually.of_forall (fun x hx => dielectric_cell d M hM hs j x hx))

theorem volumeBlock_isUnit (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M) (k : ℝ) (hk : 0<k) :
    IsUnit (DynamicVolume.volumeBlock (coefficient d M hM hs) k d.X) := by
  obtain ⟨x,hx,hout⟩ := FiniteRadialPartition.exists_exterior_seed (radii d)
    (radii_strictMono d) (radii_positive d) d.X
  exact PiecewiseMaxwellUniqueness.volumeBlock_isUnit _ k hk d.X
    (d.hR.le.trans (RadialStack.chain_ordered d.chain))
    (fun x hx => value_outer d M hM hs x (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx))
    (partition d M hM hs) _ x hx hout

end OQ14.SourceMaterialPartition

#print axioms OQ14.SourceMaterialPartition.card_eq
#print axioms OQ14.SourceMaterialPartition.radii_strictMono
#print axioms OQ14.SourceMaterialPartition.radii_positive
#print axioms OQ14.SourceMaterialPartition.exists_radius
#print axioms OQ14.SourceMaterialPartition.cell_comparisons
#print axioms OQ14.SourceMaterialPartition.sigmaAt_eq_of_comparisons
#print axioms OQ14.SourceMaterialPartition.realSigma_cell
#print axioms OQ14.SourceMaterialPartition.cellValue_positive
#print axioms OQ14.SourceMaterialPartition.dielectric_cell
#print axioms OQ14.SourceMaterialPartition.partition
#print axioms OQ14.SourceMaterialPartition.volumeBlock_isUnit
