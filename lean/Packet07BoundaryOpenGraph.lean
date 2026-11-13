import Packet07BoundaryTriangular

/-! Local regular-level graphs via the inverse function theorem. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryOpenGraph
open Filter Set Packet07BoundaryTriangular
open scoped Topology

theorem regular_level_open_graph (F : Point → ℝ) (p : Point)
    (hF : ContDiffAt ℝ (⊤ : ℕ∞) F p) (hzero : F p = 0)
    (hvertical : fderiv ℝ F p (0,1) ≠ 0) :
    ∃ (g : Plane → ℝ) (V : Set Plane), IsOpen V ∧ p.1 ∈ V ∧ ContinuousOn g V ∧
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
  let φ := hder.toPartialHomeomorph G
  let V : Set Plane := (fun u : Plane => (u,(0 : ℝ))) ⁻¹' φ.target
  have hVopen : IsOpen V := φ.open_target.preimage (continuous_id.prodMk continuous_const)
  have hpV : p.1 ∈ V := by
    change (p.1,0) ∈ φ.target
    rw [← hGp]
    exact hder.image_mem_toPartialHomeomorph_target
  have hgc : ContinuousOn g V := by
    have hi : ContinuousOn inv φ.target := φ.continuousOn_symm
    have hm : ContinuousOn (fun u : Plane => (u,(0 : ℝ))) V :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hcomp : ContinuousOn (fun u : Plane => inv (u,0)) V := hi.comp hm (fun _ hu => hu)
    exact continuous_snd.continuousOn.comp hcomp (fun _ _ => mem_univ _)
  refine ⟨g,V,hVopen,hpV,hgc,?_⟩
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

end OQ14.Packet07BoundaryOpenGraph
#print axioms OQ14.Packet07BoundaryOpenGraph.regular_level_open_graph
