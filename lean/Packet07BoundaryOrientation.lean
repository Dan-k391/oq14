import Packet07BoundarySlice

/-! Derivative orientation turns a regular graph into an actual local phase side. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07BoundaryOrientation
open Filter Set Packet07BoundaryTriangular
open scoped Topology

theorem positive_orientation (F : Point → ℝ) (p : Point) (g : Plane → ℝ)
    (hF : ContDiffAt ℝ 2 F p) (hzero : F p = 0)
    (hpos : 0 < fderiv ℝ F p (0,1)) (hg : ContinuousAt g p.1)
    (hgraph : ∀ᶠ q in 𝓝 p, F q = 0 ↔ q.2 = g q.1) :
    ∀ᶠ q in 𝓝 p, (0 < F q ↔ g q.1 < q.2) := by
  have hroot : g p.1 = p.2 := by
    have h := (hgraph.self_of_nhds).mp hzero
    exact h.symm
  have hd : ContinuousAt (fun q => fderiv ℝ F q (0,1)) p :=
    (ContinuousLinearMap.apply ℝ ℝ ((0,1) : Point)).continuous.continuousAt.comp
      ((hF.fderiv_right (m := 0) (by norm_num)).continuousAt)
  have hsmooth : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 1 F q := by
    have h1 := hF.of_le (m := 1) (by norm_num)
    exact h1.eventually (by norm_num)
  have hsign : ∀ᶠ q in 𝓝 p, 0 < fderiv ℝ F q (0,1) := hd.eventually (Ioi_mem_nhds hpos)
  have hall := hsmooth.and (hsign.and hgraph)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hFball : ContDiffOn ℝ 1 F (Metric.ball p ε) := by
    intro q hq
    exact (hball hq).1.contDiffWithinAt
  have hrootcont : ContinuousAt (fun q : Point => (q.1,g q.1)) p := by
    exact continuous_fst.continuousAt.prodMk (hg.comp continuous_fst.continuousAt)
  have hrootlim : Tendsto (fun q : Point => (q.1,g q.1)) (𝓝 p) (𝓝 p) := by
    change Tendsto (fun q : Point => (q.1,g q.1)) (𝓝 p) (𝓝 (p.1,g p.1)) at hrootcont
    simpa only [hroot, Prod.mk.eta] using hrootcont
  have hrootnear : ∀ᶠ q in 𝓝 p, (q.1,g q.1) ∈ Metric.ball p ε :=
    hrootlim.eventually (Metric.ball_mem_nhds p hε)
  filter_upwards [Metric.ball_mem_nhds p hε,hrootnear] with q hq hr
  have hrootF : F (q.1,g q.1) = 0 := ((hball hr).2.2).mpr rfl
  let lo := min q.2 (g q.1)
  let hi := max q.2 (g q.1)
  have hseg : ∀ t ∈ Icc lo hi, (q.1,t) ∈ Metric.ball p ε := by
    intro t ht
    have htseg : t ∈ segment ℝ q.2 (g q.1) := by
      rw [segment_eq_Icc']
      exact ht
    rw [segment_eq_image] at htseg
    obtain ⟨a,⟨ha0,ha1⟩,ha⟩ := htseg
    have hp : (q.1,t) = (1-a) • q + a • (q.1,g q.1) := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      · rw [← add_smul]; simp
      · exact ha.symm
    rw [hp]
    exact (convex_ball p ε) hq hr (sub_nonneg.mpr ha1) ha0 (by ring)
  have hder : ∀ t ∈ Icc lo hi, 0 < fderiv ℝ F (q.1,t) (0,1) :=
    fun t ht => (hball (hseg t ht)).2.1
  exact Packet07BoundarySlice.positive_slice F (Metric.ball p ε) Metric.isOpen_ball hFball q.1 lo hi q.2 (g q.1)
    (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _) hseg hder hrootF

theorem negative_orientation (F : Point → ℝ) (p : Point) (g : Plane → ℝ)
    (hF : ContDiffAt ℝ 2 F p) (hzero : F p = 0)
    (hneg : fderiv ℝ F p (0,1) < 0) (hg : ContinuousAt g p.1)
    (hgraph : ∀ᶠ q in 𝓝 p, F q = 0 ↔ q.2 = g q.1) :
    ∀ᶠ q in 𝓝 p, (0 < F q ↔ q.2 < g q.1) := by
  have hroot : g p.1 = p.2 := by
    have h := (hgraph.self_of_nhds).mp hzero
    exact h.symm
  have hd : ContinuousAt (fun q => fderiv ℝ F q (0,1)) p :=
    (ContinuousLinearMap.apply ℝ ℝ ((0,1) : Point)).continuous.continuousAt.comp
      ((hF.fderiv_right (m := 0) (by norm_num)).continuousAt)
  have hsmooth : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 1 F q := by
    have h1 := hF.of_le (m := 1) (by norm_num)
    exact h1.eventually (by norm_num)
  have hsign : ∀ᶠ q in 𝓝 p, fderiv ℝ F q (0,1) < 0 := hd.eventually (Iio_mem_nhds hneg)
  have hall := hsmooth.and (hsign.and hgraph)
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hall
  have hFball : ContDiffOn ℝ 1 F (Metric.ball p ε) := by
    intro q hq
    exact (hball hq).1.contDiffWithinAt
  have hrootcont : ContinuousAt (fun q : Point => (q.1,g q.1)) p := by
    exact continuous_fst.continuousAt.prodMk (hg.comp continuous_fst.continuousAt)
  have hrootlim : Tendsto (fun q : Point => (q.1,g q.1)) (𝓝 p) (𝓝 p) := by
    change Tendsto (fun q : Point => (q.1,g q.1)) (𝓝 p) (𝓝 (p.1,g p.1)) at hrootcont
    simpa only [hroot, Prod.mk.eta] using hrootcont
  have hrootnear : ∀ᶠ q in 𝓝 p, (q.1,g q.1) ∈ Metric.ball p ε :=
    hrootlim.eventually (Metric.ball_mem_nhds p hε)
  filter_upwards [Metric.ball_mem_nhds p hε,hrootnear] with q hq hr
  have hrootF : F (q.1,g q.1) = 0 := ((hball hr).2.2).mpr rfl
  let lo := min q.2 (g q.1)
  let hi := max q.2 (g q.1)
  have hseg : ∀ t ∈ Icc lo hi, (q.1,t) ∈ Metric.ball p ε := by
    intro t ht
    have htseg : t ∈ segment ℝ q.2 (g q.1) := by
      rw [segment_eq_Icc']
      exact ht
    rw [segment_eq_image] at htseg
    obtain ⟨a,⟨ha0,ha1⟩,ha⟩ := htseg
    have hp : (q.1,t) = (1-a) • q + a • (q.1,g q.1) := by
      ext <;> simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
      · rw [← add_smul]; simp
      · exact ha.symm
    rw [hp]
    exact (convex_ball p ε) hq hr (sub_nonneg.mpr ha1) ha0 (by ring)
  have hder : ∀ t ∈ Icc lo hi, fderiv ℝ F (q.1,t) (0,1) < 0 :=
    fun t ht => (hball (hseg t ht)).2.1
  exact Packet07BoundarySlice.negative_slice F (Metric.ball p ε) Metric.isOpen_ball hFball q.1 lo hi q.2 (g q.1)
    (min_le_left _ _) (le_max_left _ _) (min_le_right _ _) (le_max_right _ _) hseg hder hrootF

end OQ14.Packet07BoundaryOrientation
#print axioms OQ14.Packet07BoundaryOrientation.positive_orientation
#print axioms OQ14.Packet07BoundaryOrientation.negative_orientation
