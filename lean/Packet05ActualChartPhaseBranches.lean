import Packet05ChartElectricIdentity

/-! Continuous graph-phase branches agree with the actual physical electric
field under the signed chart, not merely with an abstract scalar expression. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ActualChartPhaseBranches
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakDivergence OQ14.Packet05ChartElectricIdentity
  OQ14.Packet05ChartCorrectionContinuous OQ14.Packet05GraphPhaseReconstruction
  OQ14.Packet05GraphPullback OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05ScalarDielectricFlux OQ14.Packet05FlatWeight
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_chart_phase_branches (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (G Q : L2Vector) (B : Fin 3 → ℝ) (hB : ∀ j x, ‖slopeC g j x‖ ≤ B j)
    (A : Fin 3 → Fin 3 → Test) (d : ℝ) (hd : 0 ≤ d) (T : Set Maxwell.Space) (hT : IsOpen T)
    (ε : ℂ) (hε : ε ≠ 0) (hweight : ∀ x ∈ T, weight d x = ε)
    (hmetric : ∀ x ∈ T, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (χ : ContDiffBump (0 : Maxwell.Space)) (W : Field) (hW : ∀ j, Continuous (fun x => W x j))
    (Qeq : Q = chartVector up i (Packet06ScalarGaussLocalization.correction χ W hW))
    (E : Field) (Gphys Qphys : L2Vector) (hG : G = chartVector up i Gphys)
    (hQphys : Qphys = Packet06ScalarGaussLocalization.correction χ W hW)
    (Ω : Set Maxwell.Space)
    (hmap : ∀ x ∈ T, inverseOriented up i (graphMap (liftedHeight g) x) ∈ Ω)
    (hE : ∀ j, ∀ᵐ y ∂volume, y ∈ Ω → Gphys j y+Qphys j y=E y j)
    (f0 f1 fn : Maxwell.Space → ℂ) (hf0 : Continuous f0) (hf1 : Continuous f1) (hfn : Continuous fn)
    (h0 : (fun x => pulledGradient g hg G B hB 0 x) =ᵐ[volume.restrict T] f0)
    (h1 : (fun x => pulledGradient g hg G B hB 1 x) =ᵐ[volume.restrict T] f1)
    (hn : (fun x => (flux A (pulledGradient g hg G B hB) d hd 2 -
      (-mulWeight d hd (transformedFlux g hg Q B hB 2)) : L2Scalar) x) =ᵐ[volume.restrict T] fn) :
    ∃ reps : Fin 3 → Maxwell.Space → ℂ, (∀ j, Continuous (reps j)) ∧
      ∀ j, (fun x => orientedElectric up i g E x j) =ᵐ[volume.restrict T] reps j := by
  let w := chartCorrection up i g χ W
  have hw : ∀ j, Continuous (w j) := fun j => chartCorrection_continuous up i g hg χ W hW j
  have hQ : ∀ j, (fun x => pullback g hg.continuous (Q j) x) =ᵐ[volume.restrict T] w j := by
    intro j
    rw [Qeq]
    exact ae_restrict_of_ae (chartCorrection_ae up i g hg χ W hW j)
  obtain ⟨reps,hreps,hrepAE⟩ := graph_phase_reconstruction g hg G Q B hB A d hd T hT ε hε
    hweight hmetric w hw hQ f0 f1 fn hf0 hf1 hfn h0 h1 hn
  refine ⟨reps,hreps,?_⟩
  intro j
  have he := chart_electric_ae up i g hg Ω T hT Gphys Qphys E hmap hE j
  rw [← hG, hQphys, ← Qeq] at he
  exact he.symm.trans (hrepAE j)

end OQ14.Packet05ActualChartPhaseBranches
#print axioms OQ14.Packet05ActualChartPhaseBranches.actual_chart_phase_branches
