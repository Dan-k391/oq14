import Packet07DrivenUniformReference
import Packet05ChartH2Uniform
import Packet05UniformGraphForcing
import Packet05SlopeUniformBounds
import Packet05GraphSlopeBounds

/-! Fixed graph forcing bounds for the literal driven sequence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet07DrivenUniformForcing
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  ConicalGradientGraph Packet05ChartWeakDivergence Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence
  Packet05PhysicalGraphChart Packet05FlatWeight Packet05ChartBasis
open scoped Topology
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

theorem actual_graph_forcing {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (input : Input)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (χ : ContDiffBump (0 : Space)) (f : Plane → ℝ) (hf : ContDiff ℝ 4 f)
    (hfc : HasCompactSupport f) (up : Bool) (axis : Fin 3) (jump : ℝ) (hj : 0 ≤ jump) :
    let W : ℕ → Field := fun j x i => (FiniteAngularHerglotz.incident k input).E x i +
      Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source (g.rounded j)
        (Packet07SelectedRadiation.actualUnknown g k j input)) x i
    ∃ hW : ∀ j i, Continuous (fun x => W j x i),
    ∃ (B L1 L2 KF : ℝ) (hB : ∀ i x, ‖slopeC f i x‖ ≤ B),
      0 ≤ B ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧ 0 ≤ KF ∧
      (∀ i j, MemLp (fun x => dcoord (slopeC f i) x j) ⊤ volume) ∧
      (∀ i j l, MemLp (fun x => dcoord (fun y => dcoord (slopeC f i) y j) x l) ⊤ volume) ∧
      (∀ i j x, ‖dcoord (slopeC f i) x j‖ ≤ L1) ∧
      (∀ i j l x, ‖dcoord (fun y => dcoord (slopeC f i) y j) x l‖ ≤ L2) ∧
      ∀ j : ℕ,
        let Q := chartVector up axis (Packet06ScalarGaussLocalization.correction χ (W j) (hW j))
        let hg : ContDiff ℝ 2 f := hf.of_le (by decide)
        let F : L2Vector := fun l => -mulWeight jump hj (transformedFlux f hg Q (fun _ => B) hB l)
        ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
          (∀ l, CompactRepresentative (F l)) ∧
          (∀ i, i ≠ 2 → ∀ l, HasWeakPartial (F l) (F1 i l) i) ∧
          (∀ i, i ≠ 2 → ∀ m, m ≠ 2 → ∀ l, HasWeakPartial (F1 i l) (F2 i m l) m) ∧
          (∑ l : Fin 3, ‖F l‖) ≤ KF ∧ (∀ i, (∑ l : Fin 3, ‖F1 i l‖) ≤ KF) ∧
          (∀ i m, (∑ l : Fin 3, ‖F2 i m l‖) ≤ KF) := by
  classical
  obtain ⟨hW,C,hC,hcorr⟩ := Packet07DrivenUniformActual.actual_driven_correction g k input hk χ
  obtain ⟨B,L1,L2,hB0,hL10,hL20,hB,hL1,hL2⟩ := Packet05SlopeUniformBounds.slope_uniform_bounds f (hf.of_le (by decide)) hfc
  obtain ⟨_,hdi,hdd⟩ := Packet05GraphSlopeBounds.slope_bounds f (hf.of_le (by decide)) hfc
  let K0 := 3*(1+jump)*(1+3*B)*C
  let K1 := 3*(1+jump)*((1+B)+3*(B*(1+B)+L1))*C
  let K2 := 3*(1+jump)*(((1+B)^2+L1)+3*(B*((1+B)^2+L1)+2*L1*(1+B)+L2))*C
  let KF := max K0 (max K1 K2)
  have hKF : 0 ≤ KF := by dsimp [KF,K0,K1,K2]; positivity
  refine ⟨hW,B,L1,L2,KF,hB,hB0,hL10,hL20,hKF,hdi,hdd,hL1,hL2,?_⟩
  intro j
  dsimp only
  let W : Field := fun x i => (FiniteAngularHerglotz.incident k input).E x i +
    Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source (g.rounded j)
      (Packet07SelectedRadiation.actualUnknown g k j input)) x i
  let Q := Packet06ScalarGaussLocalization.correction χ W (hW j)
  have hQc (l : Fin 3) : CompactRepresentative (Q l) := by
    refine ⟨fun x => bump χ x*W x l,
      ((χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right),?_⟩
    exact Packet06ScalarGaussLocalization.correction_ae χ W (hW j) l
  choose D T hD hT hQn hDn hTn using hcorr j
  obtain ⟨QG,QH,hQc',hQG,hQH,hQn',hQGn,hQHn⟩ :=
    Packet05ChartH2Uniform.chart_vector_h2_uniform up axis Q D T hQc hD hT C hQn hDn hTn
  obtain ⟨F1,F2,hFc,hF1,hF2,hFn,hF1n,hF2n⟩ :=
    Packet05UniformGraphForcing.graph_binary_forcing_uniform f (hf.of_le (by decide))
      (chartVector up axis Q) QG QH hQc' hQG hQH C B L1 L2 hQn' hQGn hQHn hB hdi hdd hL1 hL2 jump hj
  exact ⟨F1,F2,hFc,hF1,hF2,hFn.trans (le_max_left _ _),
    fun i => (hF1n i).trans ((le_max_left _ _).trans (le_max_right _ _)),
    fun i m => (hF2n i m).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
end OQ14.Packet07DrivenUniformForcing
#print axioms OQ14.Packet07DrivenUniformForcing.actual_graph_forcing
