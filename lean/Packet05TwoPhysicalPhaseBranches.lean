import Packet05PhysicalChartBranches

/-! Both one-sided physical field branches on a graph neighborhood, with the
upper and lower binary dielectric values and exact signed-coordinate map. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05TwoPhysicalPhaseBranches
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05ChartBasis OQ14.Packet05ChartWeakDivergence
  OQ14.Packet05ActualChartPhaseBranches OQ14.Packet05PhysicalChartBranches
  OQ14.Packet05GraphPullback OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05ScalarDielectricFlux OQ14.Packet05FlatWeight
  OQ14.Packet05GraphChartMap OQ14.Packet05PhysicalGraphChart
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem two_physical_phase_branches (up : Bool) (i : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (G Q : L2Vector) (B : Fin 3 → ℝ) (hB : ∀ j x, ‖slopeC g j x‖ ≤ B j)
    (A : Fin 3 → Fin 3 → Test) (d : ℝ) (hd : 0 ≤ d) (T : Set Maxwell.Space) (hT : IsOpen T)
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
    ∃ lower upper : Fin 3 → Maxwell.Space → ℂ,
      (∀ j, Continuous (lower j)) ∧ (∀ j, Continuous (upper j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict
        (physicalFlatMap up i g ⁻¹' (T ∩ {x | x 2 < 0}))] lower j) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict
        (physicalFlatMap up i g ⁻¹' (T ∩ {x | 0 < x 2}))] upper j) := by
  let Tlo : Set Maxwell.Space := T ∩ {x | x 2 < 0}
  let Thi : Set Maxwell.Space := T ∩ {x | 0 < x 2}
  have hopenlo : IsOpen Tlo := hT.inter (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const)
  have hopenhi : IsOpen Thi := hT.inter (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous)
  have hlo : ∀ x ∈ Tlo, weight d x = (1 : ℂ) := by
    intro x hx
    change x ∈ T ∧ x 2 < 0 at hx
    simp [weight,FlatDifferenceCoercivity.dielectric,hx.2]
  have hhi : ∀ x ∈ Thi, weight d x = (1+d : ℂ) := by
    intro x hx
    have hn : ¬x 2 < 0 := not_lt_of_ge hx.2.le
    simp [weight,FlatDifferenceCoercivity.dielectric,hn]
  have hne : (1+d : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < 1+d by linarith))
  have hmaplo : ∀ x ∈ Tlo, inverseOriented up i (graphMap (liftedHeight g) x) ∈ Ω :=
    fun x hx => hmap x hx.1
  have hmaphi : ∀ x ∈ Thi, inverseOriented up i (graphMap (liftedHeight g) x) ∈ Ω :=
    fun x hx => hmap x hx.1
  have hmlo : ∀ x ∈ Tlo, ∀ j k, (A j k).function x = _ := fun x hx => hmetric x hx.1
  have hmhi : ∀ x ∈ Thi, ∀ j k, (A j k).function x = _ := fun x hx => hmetric x hx.1
  obtain ⟨rl,hrl,hal⟩ := actual_chart_phase_branches up i g hg G Q B hB A d hd Tlo hopenlo 1 (by norm_num)
    hlo hmlo χ W hW Qeq E Gphys Qphys hG hQphys Ω hmaplo hE f0 f1 fn hf0 hf1 hfn
    (ae_restrict_of_ae_restrict_of_subset (inter_subset_left) h0)
    (ae_restrict_of_ae_restrict_of_subset (inter_subset_left) h1)
    (ae_restrict_of_ae_restrict_of_subset (inter_subset_left) hn)
  obtain ⟨rh,hrh,hah⟩ := actual_chart_phase_branches up i g hg G Q B hB A d hd Thi hopenhi (1+d : ℂ) hne
    hhi hmhi χ W hW Qeq E Gphys Qphys hG hQphys Ω hmaphi hE f0 f1 fn hf0 hf1 hfn
    (ae_restrict_of_ae_restrict_of_subset (inter_subset_left) h0)
    (ae_restrict_of_ae_restrict_of_subset (inter_subset_left) h1)
    (ae_restrict_of_ae_restrict_of_subset (inter_subset_left) hn)
  obtain ⟨lower,hlc,hlae⟩ := physical_chart_branches up i g (hg.of_le (by decide)) Tlo hopenlo.measurableSet E rl hrl hal
  obtain ⟨upper,huc,huae⟩ := physical_chart_branches up i g (hg.of_le (by decide)) Thi hopenhi.measurableSet E rh hrh hah
  exact ⟨lower,upper,hlc,huc,hlae,huae⟩

end OQ14.Packet05TwoPhysicalPhaseBranches
#print axioms OQ14.Packet05TwoPhysicalPhaseBranches.two_physical_phase_branches
