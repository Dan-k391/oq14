import Packet05BoundedMultiplierH2
import Packet05GraphWeakDivergence

/-! The Piola transform preserves H² for a vector field across a smooth graph.
This is the regularity needed for the actual transformed correction forcing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05GraphPiolaH2
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphH1Pullback
  OQ14.Packet05GraphH2Pullback OQ14.Packet05GraphPullback OQ14.Packet05GraphWeakDivergence
  OQ14.Packet05BoundedWeakMultiplier OQ14.Packet05BoundedMultiplierH2
open OQ14.Packet05GraphSmooth OQ14.Packet05GraphSlope
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def HasH2 (u : L2Scalar) : Prop := ∃ G : L2Vector, ∃ H : Fin 3 → L2Vector,
  (∀ i, HasWeakPartial u (G i) i) ∧ ∀ i j, HasWeakPartial (G i) (H i j) j

theorem weak_partial_sub (u v Du Dv : L2Scalar) (i : Fin 3)
    (hu : HasWeakPartial u Du i) (hv : HasWeakPartial v Dv i) :
    HasWeakPartial (u-v) (Du-Dv) i := by
  intro φ
  have h1 := hu φ
  have h2 := hv φ
  simp only [map_sub]
  linear_combination h1-h2

theorem h2_sub (u v : L2Scalar) (hu : HasH2 u) (hv : HasH2 v) : HasH2 (u-v) := by
  obtain ⟨G,H,hG,hH⟩ := hu
  obtain ⟨G',H',hG',hH'⟩ := hv
  exact ⟨fun i => G i-G' i, fun i j => H i j-H' i j,
    fun i => weak_partial_sub _ _ _ _ i (hG i) (hG' i),
    fun i j => weak_partial_sub _ _ _ _ j (hH i j) (hH' i j)⟩

theorem slopeC_contDiff2 (g : Plane → ℝ) (hg : ContDiff ℝ 3 g) (i : Fin 3) :
    ContDiff ℝ 2 (slopeC g i) := by
  have hs : ContDiff ℝ 2 (slope g i) := by
    exact ((liftedHeight_contDiff g hg).contDiff_fderiv_apply (by norm_num)).comp
      (contDiff_id.prodMk contDiff_const)
  exact Complex.ofRealCLM.contDiff.comp hs

theorem graph_piola_h2 (g : Plane → ℝ) (hg3 : ContDiff ℝ 3 g) (P : L2Vector)
    (hP : ∀ i, HasH2 (P i)) (B : Fin 3 → ℝ)
    (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i)
    (hdi : ∀ i j, MemLp (fun x => dcoord (slopeC g i) x j) ⊤ volume)
    (hdd : ∀ i j k, MemLp (fun x => dcoord (fun y => dcoord (slopeC g i) y j) x k) ⊤ volume) :
    let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
    ∀ j, HasH2 (transformedFlux g hg P B hB j) := by
  dsimp only
  let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
  have hp (i : Fin 3) : HasH2 (pullback g hg.continuous (P i)) := by
    obtain ⟨G,H,hG,hH⟩ := hP i
    obtain ⟨K,h1,h2⟩ := graph_pullback_h2 g hg (P i) G H hG hH B hB hdi
    exact ⟨pulledGradient g hg G B hB, K, h1, h2⟩
  have hm (i : Fin 3) : HasH2 (slopeMul g hg i (B i) (hB i)
      (pullback g hg.continuous (P i))) := by
    obtain ⟨G,H,hG,hH⟩ := hp i
    exact bounded_multiplier_h2 _ (slopeC_contDiff2 g hg3 i)
      (slopeC_memLp_top g hg i (B i) (hB i)) (hdi i) (hdd i) _ G H hG hH
  intro j
  by_cases hj : j = 2
  · simp only [transformedFlux, hj, ↓reduceIte]
    exact h2_sub _ _ (h2_sub _ _ (h2_sub _ _ (hp 2) (hm 0)) (hm 1)) (hm 2)
  · simpa only [transformedFlux, hj, ↓reduceIte] using hp j

end OQ14.Packet05GraphPiolaH2
#print axioms OQ14.Packet05GraphPiolaH2.weak_partial_sub
#print axioms OQ14.Packet05GraphPiolaH2.h2_sub
#print axioms OQ14.Packet05GraphPiolaH2.slopeC_contDiff2
#print axioms OQ14.Packet05GraphPiolaH2.graph_piola_h2
