import Packet05FixedChartIteration
import Packet05NestedBootstrapPhysicalBranch
import Packet05DivergenceZeroRegion
import Packet05ActualFieldIdentity
import Packet05PhaseWeightBound

/-! Uniform actual rounded-mode physical fields on both sides of a fixed
material chart. All cutoffs and constants are chosen before the family index. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option synthInstance.maxHeartbeats 800000
namespace OQ14.Packet05FixedChartUniformField
open MeasureTheory Metric Set Filter Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  ConicalGradientGraph Packet05RegionalPartial Packet05RegionalDivergence Packet05DivergenceZeroRegion
  Packet05RegionalScalarLocalization Packet05RegionalFluxCutoff Packet05ScalarCutoffTransfer
  Packet05ScalarDielectricFlux Packet05GraphSlopeMultiplier Packet05GraphWeakDivergence Packet05GraphH1Pullback
  Packet05GraphPullback Packet05ChartWeakGradient Packet05ChartWeakDivergence Packet05ChartBasis
  Packet05GraphChartMap Packet05PhysicalGraphChart Packet05PhysicalChartBranches Packet05FlatWeight
  Packet05ChartCorrectionContinuous Packet05FiniteFixedAtlas Packet06ConcreteModalRounding Packet05ActualChartFields
  Packet05NestedCutoffSupport Packet05FiveNestedCutoffs MaxwellCutoffCommutator Packet05MatrixWeakDerivative
open scoped Topology
abbrev Space := Maxwell.Space

theorem fixed_chart_uniform_field {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (chart : Chart n hn g η hη) (p : Space) (hp : p ∈ chart.flat)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z0 : ℂ) (v0 : Packet06SectorOperator.Sector) (hzlim : Tendsto z atTop (𝓝 z0))
    (hvlim : Tendsto v atTop (𝓝 v0)) (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0) :
    ∃ (T : Set Space) (Cbound : ℝ), IsOpen T ∧ p ∈ T ∧ T ⊆ chart.flat ∧ 0 ≤ Cbound ∧
      ∀ᶠ j in atTop, ∃ lower upper : Fin 3 → Space → ℂ,
        (∀ k, Continuous (lower k)) ∧ (∀ k, Continuous (upper k)) ∧
        (∀ k, (fun x => Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) x k) =ᵐ[volume.restrict
            (physicalFlatMap chart.up chart.axis chart.graph ⁻¹' (T ∩ {x | x 2 < 0}))] lower k) ∧
        (∀ k, (fun x => Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) x k) =ᵐ[volume.restrict
            (physicalFlatMap chart.up chart.axis chart.graph ⁻¹' (T ∩ {x | 0 < x 2}))] upper k) ∧
        (∀ k x, x ∈ physicalFlatMap chart.up chart.axis chart.graph ⁻¹' (T ∩ {x | x 2 < 0}) → ‖lower k x‖ ≤ Cbound) ∧
        (∀ k x, x ∈ physicalFlatMap chart.up chart.axis chart.graph ⁻¹' (T ∩ {x | 0 < x 2}) → ‖upper k x‖ ≤ Cbound) := by
  obtain ⟨R,A,q,B,K,W0,Kboot,P,Q,hB,hR,hRsub,hA3,hA,hB0,hK0,hW00,hKboot,hP,hQ,hiter⟩ :=
    Packet05FixedChartIteration.fixed_chart_iteration n hn g η hη chart p hp z v z0 v0 hzlim hvlim hz hmode
  have hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function := fun j k => (hA3 j k).of_le (by decide)
  obtain ⟨a,b,c,ha0,hb0,hc0,ha,hb,hc⟩ := Packet05MetricAllBounds.matrix_all_bounds A hA2
  obtain ⟨M,L1,L2,hM0,_,_,hMs,_,_⟩ := Packet05SlopeUniformBounds.slope_uniform_bounds chart.graph (chart.regular.of_le (by decide)) chart.compact
  have hM : ∀ x, |Packet05GraphSlope.slope chart.graph 0 x| ≤ M ∧ |Packet05GraphSlope.slope chart.graph 1 x| ≤ M := by
    intro x
    constructor <;> simpa [slopeC,Complex.norm_real,Real.norm_eq_abs] using hMs _ x
  let θ := q.q3.middle.complexTest.toTest
  let θlocal := q.q3.outer.complexTest.toTest
  let lam := q.q4.outer.complexTest.toTest
  let ξ := q.q4.inner.complexTest.toTest
  have hθ2 : ContDiff ℝ 2 θ.function := complex_regular q.q3.middle 2 (q.q3.regular 2).2.1
  have hθlocal2 : ContDiff ℝ 2 θlocal.function := complex_regular q.q3.outer 2 (q.q3.regular 2).1
  have hξ2 : ContDiff ℝ 2 ξ.function := complex_regular q.q4.inner 2 (q.q4.regular 2).2.2
  obtain ⟨α,β,γ,_,_,_,hα,hβ,hγ⟩ := Packet05CutoffSecondBound.derivative_bounds θ hθ2
  obtain ⟨αk,βk,γk,_,_,_,hαk,hβk,_⟩ := Packet05CutoffSecondBound.derivative_bounds q.q1.inner.complexTest.toTest
    (complex_regular q.q1.inner 2 (q.q1.regular 2).2.2)
  obtain ⟨aθ,bθ,cθ,_,_,_,haθ,hbθ,hcθ⟩ := Packet05CutoffSecondBound.derivative_bounds θlocal hθlocal2
  obtain ⟨r,s,t0,_,_,_,hr,hs,_⟩ := Packet05CutoffSecondBound.derivative_bounds lam
    (complex_regular q.q4.outer 2 (q.q4.regular 2).1)
  obtain ⟨pp,qq,tt,_,_,_,hpp,hqq,htt⟩ := Packet05CutoffSecondBound.derivative_bounds ξ hξ2
  have hViter : ball p (4*q.q1.r) ⊆ ball p (2*q.q0.r) := small_ball_subset q.q1 4 (by norm_num)
  have hSiter : ball p (2*q.q1.r) ⊆ ball p (4*q.q1.r) := ball_subset_ball (by linarith [q.q1.positive])
  have hVlocal : ball p (2*q.q2.r) ⊆ ball p (2*q.q1.r) := small_ball_subset q.q2 2 (by norm_num)
  have hVreg : ball p (4*q.q3.r) ⊆ ball p (2*q.q2.r) := small_ball_subset q.q3 4 (by norm_num)
  have hWreg : ball p (4*q.q4.r) ⊆ ball p (4*q.q3.r) := small_ball_subset q.q4 4 (by norm_num)
  have hT : ball p (2*q.q4.r) ⊆ ball p (4*q.q4.r) := ball_subset_ball (by linarith [q.q4.positive])
  have hTreg := hT.trans hWreg
  have hTlocal := hTreg.trans hVreg
  have hTiter := hTlocal.trans hVlocal
  have hTboot := hTiter.trans (hSiter.trans hViter)
  have hbootΩ : ball p (2*q.q0.r) ⊆ ball p R := small_ball_subset q.q0 2 (by norm_num)
  have hTΩ := hTboot.trans hbootΩ
  have hVregboot : ball p (4*q.q3.r) ⊆ ball p (2*q.q0.r) := hVreg.trans (hVlocal.trans (hSiter.trans hViter))
  have hVlocalgrad : ball p (2*q.q2.r) ⊆ ball p (4*q.q1.r) := hVlocal.trans hSiter
  have hκT : ∀ x ∈ ball p (2*q.q4.r), q.q1.inner.function x = 1 :=
    fun x hx => (q.q1.inner_one x (hTiter hx)).eq_of_nhds
  have hζV : ∀ x ∈ ball p (2*q.q2.r), q.q2.middle.function x = 1 :=
    fun x hx => q.q2.middle_one x ((ball_subset_ball (show 2*q.q2.r ≤ 4*q.q2.r by linarith [q.q2.positive])) hx)
  have hθV : tsupport θ.function ⊆ ball p (2*q.q2.r) := by
    simpa only [θ,complex_support] using middle_support q.q3
  have hθT : ∀ x ∈ ball p (2*q.q4.r), θ.function x = 1 :=
    fun x hx => real_one_complex q.q3.middle (q.q3.middle_one x (hTreg hx))
  have hθlocalV : tsupport θlocal.function ⊆ ball p (2*q.q2.r) := by
    simpa only [θlocal,complex_support] using q.q3.outer_support
  have hθlocalR : ∀ x ∈ ball p (4*q.q3.r), θlocal.function x = 1 := by
    intro x hx
    exact (q.q3.outer_one x ((ball_subset_ball (show 4*q.q3.r ≤ 8*q.q3.r by linarith [q.q3.positive])) hx)).eq_of_nhds
  have hlamR : tsupport lam.function ⊆ ball p (4*q.q3.r) := by
    simpa only [lam,complex_support] using q.q4.outer_support
  have hlamW : ∀ x ∈ ball p (4*q.q4.r), lam.function x = 1 := by
    intro x hx
    exact (q.q4.outer_one x ((ball_subset_ball (show 4*q.q4.r ≤ 8*q.q4.r by linarith [q.q4.positive])) hx)).eq_of_nhds
  have hξW : tsupport ξ.function ⊆ ball p (4*q.q4.r) := by
    simpa only [ξ,complex_support] using q.q4.inner_middle
  have hξT : ∀ x ∈ ball p (2*q.q4.r), ξ.function x = 1 := by
    intro x hx
    exact real_one_complex q.q4.inner ((q.q4.inner_one x hx).eq_of_nhds)
  have hκboot : ∀ x ∈ ball p (2*q.q4.r), q.q0.inner.function x = 1 :=
    fun x hx => (q.q0.inner_one x (hTboot hx)).eq_of_nhds
  let Larr := max (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ Kboot P Q)
    (Packet05AssembledArrayCeiling.ceiling aθ bθ cθ Kboot Kboot Kboot)
  let Tang := Packet05ExplicitAnisotropicBound.universalConstant *
    ((α+3*β+6*γ)*αk*Kboot+(α+2*β)*3*(αk*P+βk*Kboot)+6*(α*Q+β*(αk*P+βk*Kboot)))
  let X := max W0 (max Tang (Packet05NormalFluxUniformCeiling.coefficient chart.jump a b c r s pp qq tt * Larr))
  let Cbound := (2+(1+M)*(1+4*M+1))*X
  have hX0 : 0 ≤ X := hW00.trans (le_max_left _ _)
  have hCbound : 0 ≤ Cbound := by dsimp [Cbound]; positivity
  let T := ball p (2*q.q4.r)
  have hTchart : T ⊆ chart.flat := hTΩ.trans hRsub
  refine ⟨T,Cbound,isOpen_ball,mem_ball_self (by linarith [q.q4.positive]),hTchart,hCbound,?_⟩
  filter_upwards [hiter,hz,hmode] with j hj hzj hmj
  dsimp only at hj
  obtain ⟨hbootGrad,hglobalDiv,hDzero,hGn,hRn,hWn,R1,R2,hR1,hR2,hR1n,hR2n,
    D0,D1,H00,H01,H10,H11,hD0,hD1,hH00,hH01,hH10,hH11,hH00w,hH01w,hH10w,hH11w,hbounds⟩ := hj
  let u := scalar n hn g η hη z v chart j
  let C := scalarGradient n hn g η hη z v chart B hB j
  let F := graphForcing n hn g η hη z v chart B hB j
  let G := localizedGradient q.q0.inner u C
  let Rf := localizedForcing q.q0.inner A u F chart.jump chart.jump_nonneg
  let D := cutFluxSource q.q0.inner.complexTest.toTest (fun k => flux A C chart.jump chart.jump_nonneg k-F k)
  have hDreg : ∀ᵐ x ∂volume, x ∈ ball p (4*q.q3.r) → D x=0 := by
    filter_upwards [hDzero] with x hx hxV
    exact hx (hVregboot hxV)
  have hdivReg : HasDivergenceOn (ball p (4*q.q3.r)) (fun k => flux A G chart.jump chart.jump_nonneg k-Rf k) 0 :=
    global_divergence_zero_on _ _ D hglobalDiv hDreg
  let Uphys := potential n hn g η hη z v j
  let Wphys := correction n hn g η hη z v j
  let hWphys := correction_continuous n hn g η hη z v j
  let Gphys := gradient Packet05FixedCollarAtlas.outer Uphys
  let Qphys := Packet06ScalarGaussLocalization.correction Packet05FixedCollarAtlas.outer Wphys hWphys
  let Gchart := chartVector chart.up chart.axis Gphys
  let Qchart := chartVector chart.up chart.axis Qphys
  let E := Packet06ComplexElectric.electric (z j) (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
    (DynamicVolume.source (rounded n hn g η hη j) (v j))
  have hE := Packet05ActualFieldIdentity.actual_field_identity n hn g η hη z v j hzj hmj
  have hcomponent (k : Fin 3) := hbounds k
  have hD0n (k : Fin 3) : ‖D0 k‖ ≤ P := (hcomponent k).1
  have hD1n (k : Fin 3) : ‖D1 k‖ ≤ P := (hcomponent k).2.1
  have hH00n (k : Fin 3) : ‖H00 k‖ ≤ Q := (hcomponent k).2.2.1
  have hH01n (k : Fin 3) : ‖H01 k‖ ≤ Q := (hcomponent k).2.2.2.1
  have hH10n (k : Fin 3) : ‖H10 k‖ ≤ Q := (hcomponent k).2.2.2.2.1
  have hH11n (k : Fin 3) : ‖H11 k‖ ≤ Q := (hcomponent k).2.2.2.2.2
  have hinv : ‖((1+chart.jump : ℂ))⁻¹‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [chart.jump_nonneg] : 0 < 1+chart.jump)]
    exact (inv_le_one₀ (by linarith [chart.jump_nonneg] : 0 < 1+chart.jump)).2 (by linarith [chart.jump_nonneg])
  have hne : (1+chart.jump : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (show 0 < 1+chart.jump by linarith [chart.jump_nonneg]))
  have branch (Tphase : Set Space) (hphaseOpen : IsOpen Tphase) (hphaseT : Tphase ⊆ T)
      (ε : ℂ) (hε : ε ≠ 0) (hεinv : ‖ε⁻¹‖ ≤ 1)
      (hweight : ∀ x ∈ Tphase, weight chart.jump x = ε) :
      ∃ reps : Fin 3 → Space → ℂ, (∀ k, Continuous (reps k)) ∧
        (∀ k, (fun x => E x k) =ᵐ[volume.restrict (physicalFlatMap chart.up chart.axis chart.graph ⁻¹' Tphase)] reps k) ∧
        ∀ k x, x ∈ physicalFlatMap chart.up chart.axis chart.graph ⁻¹' Tphase → ‖reps k x‖ ≤ Cbound := by
    apply Packet05NestedBootstrapPhysicalBranch.nested_bootstrap_physical_branch chart.up chart.axis chart.graph
      (chart.regular.of_le (by decide)) Gchart Qchart (fun _ => B) hB A hA2 hA3 chart.jump chart.jump_nonneg
      Tphase hphaseOpen ε hε hweight (fun x hx => hA x (hTΩ (hphaseT hx)))
      Packet05FixedCollarAtlas.outer Wphys hWphys rfl E Gphys Qphys rfl rfl (ball (0 : Space) Packet05FixedCollarAtlas.outer.rIn)
      (fun x hx => chart.maps_outer x (hTchart (hphaseT hx))) hE
      q.q0.inner (fun x hx => hκboot x (hphaseT hx)) u hbootGrad
      (ball p (4*q.q1.r)) (ball p (2*q.q2.r)) (ball p (4*q.q3.r)) (ball p (4*q.q4.r))
      isOpen_ball isOpen_ball hVlocalgrad isOpen_ball hWreg hdivReg D0 D1 H00 H01 H10 H11 hD0 hD1 hH00 hH01 hH10 hH11
      q.q1.inner q.q2.middle q.q1.inner_middle (fun x hx => hκT x (hphaseT hx)) hζV hH00w hH01w hH10w hH11w
      R1 R2 hR1 hR2 Kboot P Q hKboot hP hQ hGn hRn hD0n hD1n hH00n hH01n hH10n hH11n hR1n hR2n
      θ hθV (fun x hx => hθT x (hphaseT hx)) hθ2 α β γ αk βk hα hβ hγ hαk hβk
      θlocal hθlocal2 hθlocalV hθlocalR aθ bθ cθ haθ hbθ hcθ lam ξ hlamR hlamW hξW hξ2
      (fun x hx => hξT x (hphaseT hx)) (hphaseT.trans hT) a b c r s pp qq tt ha hb (fun j k l m x => hc j k l m x)
      hr hs hpp hqq htt M 1 W0 hM0 hεinv (fun x hx => hM x)
      (fun x hx k => hWn x (hTΩ (hphaseT hx)) k)
  let Tlo : Set Space := T ∩ {x | x 2 < 0}
  let Thi : Set Space := T ∩ {x | 0 < x 2}
  have hlo : IsOpen Tlo := isOpen_ball.inter (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const)
  have hhi : IsOpen Thi := isOpen_ball.inter (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous)
  have hwlo : ∀ x ∈ Tlo, weight chart.jump x = (1 : ℂ) := by
    intro x hx
    change x ∈ T ∧ x 2 < 0 at hx
    simp [weight,FlatDifferenceCoercivity.dielectric,hx.2]
  have hwhi : ∀ x ∈ Thi, weight chart.jump x = (1+chart.jump : ℂ) := by
    intro x hx
    have hnot : ¬ x 2 < 0 := not_lt_of_ge hx.2.le
    simp [weight,FlatDifferenceCoercivity.dielectric,hnot]
  obtain ⟨lower,hl,hlae,hlb⟩ := branch Tlo hlo inter_subset_left 1 (by norm_num) (by norm_num) hwlo
  obtain ⟨upper,hu,huae,hub⟩ := branch Thi hhi inter_subset_left (1+chart.jump : ℂ) hne hinv hwhi
  exact ⟨lower,upper,hl,hu,hlae,huae,hlb,hub⟩

end OQ14.Packet05FixedChartUniformField
#print axioms OQ14.Packet05FixedChartUniformField.fixed_chart_uniform_field
