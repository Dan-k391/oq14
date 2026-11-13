import Packet07BoundaryTriangular

/-! Local regular-level graphs via the inverse function theorem. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryGraph
open Filter Set Packet07BoundaryTriangular
open scoped Topology

theorem regular_level_graph (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F p) (hzero : F p = 0)
    (hvertical : fderiv ℝ F p (0,1) ≠ 0) :
    ∃ g : Plane → ℝ, ContinuousAt g p.1 ∧
      (∀ᶠ q in 𝓝 p, F q = 0 ↔ q.2 = g q.1) := by
  let D := fderiv ℝ F p
  let T := triangular D
  have hb := triangular_bijective D hvertical
  let e : Point ≃L[ℝ] Point := ContinuousLinearEquiv.ofBijective T
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  let G : Point → Point := fun q => (q.1,F q)
  have hder : HasStrictFDerivAt G (e : Point →L[ℝ] Point) p := by
    have hf := hF.hasStrictFDerivAt (by simp)
    have hp := (ContinuousLinearMap.fst ℝ Plane ℝ).hasStrictFDerivAt.prodMk hf
    change HasStrictFDerivAt G T p at hp
    exact hp
  let inv := hder.localInverse G e p
  let g : Plane → ℝ := fun u => (inv (u,0)).2
  have hGp : G p = (p.1,0) := by simp [G,hzero]
  have hgc : ContinuousAt g p.1 := by
    have hi := hder.localInverse_continuousAt
    rw [hGp] at hi
    have hm : ContinuousAt (fun u : Plane => (u,(0 : ℝ))) p.1 :=
      continuousAt_id.prodMk continuousAt_const
    have hi' : ContinuousAt (fun u : Plane => inv (u,0)) p.1 := ContinuousAt.comp (f := fun u : Plane => (u,(0 : ℝ))) (x := p.1) hi hm
    exact continuous_snd.continuousAt.comp hi'
  refine ⟨g,hgc,?_⟩
  have hleft := hder.eventually_left_inverse
  have hright := hder.eventually_right_inverse
  rw [hGp] at hright
  have hright' : ∀ᶠ q : Point in 𝓝 p, G (inv (q.1,0)) = (q.1,0) := by
    have hmap : Tendsto (fun q : Point => (q.1,(0 : ℝ))) (𝓝 p) (𝓝 (p.1,0)) :=
      (continuous_fst.continuousAt.prodMk continuousAt_const)
    exact hmap.eventually hright
  filter_upwards [hleft,hright'] with q hl hr
  constructor
  · intro hz
    have he : inv (q.1,0) = q := by simpa [G,hz] using hl
    change q.2 = (inv (q.1,0)).2
    rw [he]
  · intro hz
    have he : q = inv (q.1,0) := by
      apply Prod.ext
      · have hh := congrArg Prod.fst hr
        simpa [G] using hh.symm
      · exact hz
    rw [he]
    have hh := congrArg Prod.snd hr
    simpa [G] using hh

end OQ14.Packet07BoundaryGraph
#print axioms OQ14.Packet07BoundaryGraph.regular_level_graph
