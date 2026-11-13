import Packet07BoundaryOrientation
import Packet07BoundaryC3Refined

/-! A genuine C³ chart whose two sides are the actual binary phases. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07BoundaryC3Oriented
open Filter Set Packet07BoundaryCoordinates
open scoped Topology

theorem oriented_chart_of_regular_boundary (B : Set Space) (x : Space)
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ B ↔ 0 < F y)) :
    ∃ (i : Fin 3) (g : Plane → ℝ) (V : Set Plane) (up : Bool),
      IsOpen V ∧ (chart i x).1 ∈ V ∧ ContDiffOn ℝ 3 g V ∧
      (∀ᶠ y in 𝓝 x, (chart i y).1 ∈ V ∧
        (y ∈ B ↔ if up then g (chart i y).1 < (chart i y).2
          else (chart i y).2 < g (chart i y).1)) := by
  obtain ⟨F,i,g,V,W,hi,hV,hxV,hg,hW,hxW,hFs,h0,hD,hlocal⟩ :=
    Packet07BoundaryC3Refined.chart_of_regular_boundary B x hcert
  let q := chart i x
  let H : Point → ℝ := fun p => F (unchart i p)
  have hqx : unchart i q = x := unchart_chart i x
  have hFat : ContDiffAt ℝ 2 F x := (hFs.contDiffAt (hW.mem_nhds hxW)).of_le (by change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((3 : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr (by norm_num))
  have hH : ContDiffAt ℝ 2 H q := by
    change ContDiffAt ℝ 2 (F ∘ unchart i) q
    apply ContDiffAt.comp q
    · simpa [hqx] using hFat
    · exact (unchartCLM i).contDiff.contDiffAt
  have hd : fderiv ℝ H q (0,1) = fderiv ℝ F x (EuclideanSpace.single i 1) := by
    have hf : HasFDerivAt F (fderiv ℝ F x) (unchart i q) := by
      rw [hqx]
      exact (hFat.differentiableAt (by norm_num)).hasFDerivAt
    have hh := hf.comp q (unchartCLM i).hasFDerivAt
    change HasFDerivAt H ((fderiv ℝ F x).comp (unchartCLM i)) q at hh
    rw [hh.fderiv]
    change fderiv ℝ F x (unchart i (0,1)) = _
    rw [unchart_vertical]
  have hgAt : ContinuousAt g q.1 := (hg.contDiffAt (hV.mem_nhds hxV)).continuousAt
  have hgraph : ∀ᶠ p in 𝓝 q, H p = 0 ↔ p.2 = g p.1 := by
    have hu : ContinuousAt (unchart i) q := (unchartCLM i).continuous.continuousAt
    have hw : W ∈ 𝓝 (unchart i q) := by simpa [hqx] using hW.mem_nhds hxW
    have hh := hu.tendsto.eventually hw
    filter_upwards [hh] with p hp
    have h := (hlocal (unchart i p) hp).2
    simpa only [H, chart_unchart] using h
  have hchart : ContinuousAt (chart i) x :=
    ConicalJunctionPhysical.split_continuous.continuousAt.comp (swapCLM i).continuous.continuousAt
  have hVnear : ∀ᶠ y in 𝓝 x, (chart i y).1 ∈ V :=
    (continuous_fst.continuousAt.comp hchart).tendsto.eventually (hV.mem_nhds hxV)
  rcases lt_or_gt_of_ne hi with hn | hp
  · have hneg : fderiv ℝ H q (0,1) < 0 := by rw [hd]; exact hn
    have horient := Packet07BoundaryOrientation.negative_orientation H q g
      hH (by simpa [H,hqx] using h0) hneg hgAt hgraph
    have hy := hchart.tendsto.eventually horient
    refine ⟨i,g,V,false,hV,hxV,hg,?_⟩
    filter_upwards [hVnear, hW.mem_nhds hxW, hy] with y hyV hyW hyorient
    refine ⟨hyV, ?_⟩
    have he : (0 < F y ↔ (chart i y).2 < g (chart i y).1) := by
      simpa only [H, unchart_chart] using hyorient
    simpa only [Bool.false_eq_true, ite_false] using (hlocal y hyW).1.trans he
  · have hpos : 0 < fderiv ℝ H q (0,1) := by rw [hd]; exact hp
    have horient := Packet07BoundaryOrientation.positive_orientation H q g
      hH (by simpa [H,hqx] using h0) hpos hgAt hgraph
    have hy := hchart.tendsto.eventually horient
    refine ⟨i,g,V,true,hV,hxV,hg,?_⟩
    filter_upwards [hVnear, hW.mem_nhds hxW, hy] with y hyV hyW hyorient
    refine ⟨hyV, ?_⟩
    have he : (0 < F y ↔ g (chart i y).1 < (chart i y).2) := by
      simpa only [H, unchart_chart] using hyorient
    simpa only [ite_true] using (hlocal y hyW).1.trans he

theorem actual_affine_body_oriented_charts {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ConicalStaticVolume.Data) (a : ι → ℝ) (center : ι → Space)
    (ha0 : ∀ i, 0 < a i) (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j)) (s : ℝ) (hs : s ≠ 0) (shift : Space) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ frontier (Packet07AffineGeometry.map s shift ⁻¹'
        CommonBinaryInterface.body p a center n),
      ∃ (i : Fin 3) (g : Plane → ℝ) (V : Set Plane) (up : Bool),
        IsOpen V ∧ (chart i x).1 ∈ V ∧ ContDiffOn ℝ 3 g V ∧
        (∀ᶠ y in 𝓝 x, (chart i y).1 ∈ V ∧
          (y ∈ Packet07AffineGeometry.map s shift ⁻¹' CommonBinaryInterface.body p a center n ↔
            if up then g (chart i y).1 < (chart i y).2
              else (chart i y).2 < g (chart i y).1)) := by
  filter_upwards [CommonBinaryInterface.eventually_body_smooth p a center ha0 ha hsep] with n hn x hx
  exact oriented_chart_of_regular_boundary _ x
    (Packet07AffineSmooth.smooth_boundary_preimage s hs shift _ hn x hx)
end OQ14.Packet07BoundaryC3Oriented
#print axioms OQ14.Packet07BoundaryC3Oriented.oriented_chart_of_regular_boundary
#print axioms OQ14.Packet07BoundaryC3Oriented.actual_affine_body_oriented_charts
