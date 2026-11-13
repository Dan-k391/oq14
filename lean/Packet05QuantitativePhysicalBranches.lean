import Packet05QuantitativeChartBranches
import Packet05QuantitativePhysicalChart
import Packet05QuantitativeGraphReconstruction
import Packet05ChartElectricIdentity

/-! Continuous graph-phase branches agree with the actual physical electric
field under the signed chart, not merely with an abstract scalar expression. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05QuantitativePhysicalBranches
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakDivergence OQ14.Packet05ChartElectricIdentity
  OQ14.Packet05ChartCorrectionContinuous OQ14.Packet05GraphPhaseReconstruction
  OQ14.Packet05GraphPullback OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05ScalarDielectricFlux OQ14.Packet05FlatWeight
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem quantitative_physical_branches (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
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
      (-mulWeight d hd (transformedFlux g hg Q B hB 2)) : L2Scalar) x) =ᵐ[volume.restrict T] fn)
    (M K X : ℝ) (hM : 0 ≤ M) (hK : ‖ε⁻¹‖ ≤ K)
    (hab : ∀ x ∈ T, |Packet05GraphSlope.slope g 0 x| ≤ M ∧ |Packet05GraphSlope.slope g 1 x| ≤ M)
    (hdata : ∀ x ∈ T, ‖f0 x‖ ≤ X ∧ ‖f1 x‖ ≤ X ∧ ‖fn x‖ ≤ X ∧
      ‖chartCorrection up i g χ W 0 x‖ ≤ X ∧ ‖chartCorrection up i g χ W 1 x‖ ≤ X ∧
      ‖chartCorrection up i g χ W 2 x‖ ≤ X) :
    ∃ reps : Fin 3 → Maxwell.Space → ℂ, (∀ j, Continuous (reps j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict (Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T)] reps j) ∧
      ∀ j x, x ∈ Packet05PhysicalChartBranches.physicalFlatMap up i g ⁻¹' T →
        ‖reps j x‖ ≤ (2+(1+M)*(K+4*M+1))*X := by
  obtain ⟨reps,hreps,hae,hbound⟩ := Packet05QuantitativeChartBranches.quantitative_chart_branches
    up i g hg G Q B hB A d hd T hT ε hε hweight hmetric χ W hW Qeq E Gphys Qphys hG hQphys Ω hmap hE
    f0 f1 fn hf0 hf1 hfn h0 h1 hn M K X hM hK hab hdata
  exact Packet05QuantitativePhysicalChart.quantitative_physical_chart_branches up i g
    (hg.of_le (by decide)) T hT.measurableSet E reps hreps hae _ hbound

end OQ14.Packet05QuantitativePhysicalBranches
#print axioms OQ14.Packet05QuantitativePhysicalBranches.quantitative_physical_branches
