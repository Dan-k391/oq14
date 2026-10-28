import CommonTotalErrorLocal
import ConicalLocalPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.CommonTotalPairStability
open MeasureTheory Set Metric Filter OQ14.NewtonL2 OQ14.WeakGreen OQ14.ConicalProjectionData
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev VectorL2 := VectorFourier.VectorL2

def pairMap (p : Data) (c : Space) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    VectorL2 →L[ℂ] ℂ :=
  ∑ j : Fin 3, (scalarProduct (ConicalAnnularCoefficient.testCoordinate p ζ hζ hc j)).comp
    (((StaticBallTranslation.scalar (-c)).toContinuousLinearMap).comp (DynamicConvolution.component j))

theorem pairMap_apply (p : Data) (c : Space) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) (F : VectorL2) :
    pairMap p c ζ hζ hc F = ∑ j : Fin 3, scalarProduct (ConicalAnnularCoefficient.testCoordinate p ζ hζ hc j)
      (StaticBallTranslation.scalar (-c) (physicalCoordinate F j)) := by
  simp [pairMap,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply, physicalCoordinate, DynamicConvolution.component]

theorem pair_difference (p : Data) (b : ℝ) (s t : System p b) (c : Space) (F : VectorL2)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b)
    (he : ∀ j, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate s j x-totalCoordinate t j x = physicalCoordinate F j (x+c)) :
    ConicalLocalStability.totalPair s ζ hζ hc-ConicalLocalStability.totalPair t ζ hζ hc = pairMap p c ζ hζ hc F := by
  rw [ConicalLocalStability.totalPair,ConicalLocalStability.totalPair,← Finset.sum_sub_distrib,pairMap_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← map_sub,scalarProduct_integral,scalarProduct_integral]
  apply integral_congr_ae
  filter_upwards [he j, StaticBallTranslation.scalar_ae (-c) (physicalCoordinate F j),
    Lp.coeFn_sub (totalCoordinate s j) (totalCoordinate t j),
    ConicalTangentialDivergence.tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc j]
    with x he ht hd htest
  change ConicalAnnularCoefficient.testCoordinate p ζ hζ hc j x *
    ((totalCoordinate s j-totalCoordinate t j) x) =
      ConicalAnnularCoefficient.testCoordinate p ζ hζ hc j x * StaticBallTranslation.scalar (-c) (physicalCoordinate F j) x
  rw [hd,ht]
  simp only [Pi.sub_apply,sub_neg_eq_add]
  by_cases hx : x ∈ ball (0 : Space) b
  · rw [he hx]
  · have hz : ζ ‖x‖=0 := image_eq_zero_of_nmem_tsupport (fun h => hx (by
      simpa only [mem_ball,dist_zero_right] using (hs h).2))
    change ConicalAnnularCoefficient.testCoordinate p ζ hζ hc j x = _ at htest
    rw [htest]
    simp [ConicalTangentialDivergence.tangentField,hz]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem uniform_bound (i : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hRT : R ≤ T)
    (hk : k ≠ 0) (hb : b < a i)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hKR : UnionFreeRunge.balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ (d : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
      (J : Maxwell.Field) (hJ : ∀ j, Continuous (fun x => J x j))
      (heJ : ∀ j x, x ∈ closedBall (0 : Space) b → J x j =
        ConicalCommonIncidentError.error (p i) (a i) k (center i) d j x),
      ‖ConicalLocalStability.totalPair (ConicalCommonFixedGauge.system p a center B hB hcontrast ha hsep
          i R T k b hR0 hRT hk hb hfreq hR hai d J hJ heJ) ζ hζ hc -
        ConicalLocalStability.totalPair (ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep
          i i R T k b hR0 hk hb hfreq hR hT hai) ζ hζ hc‖ ≤
      C1 * ‖ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR (hT i) d‖ +
      C2 * ‖CommonTotalError.solutionDifference p a center B hB hcontrast ha hsep i R T k hKR d‖ := by
  let P := pairMap (p i) (center i) ζ hζ hc
  let V := UnionMaterialTransfer.vector (UnionFreeRunge.balls center a) (UnionFreeRunge.balls_compact center a).measurableSet
  let D := (newtonOperator + DynamicConvolution.operator k (2*R)).comp
    (StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep))
  refine ⟨‖P‖*‖V‖,‖P‖*‖D‖,mul_nonneg (norm_nonneg _) (norm_nonneg _),
    mul_nonneg (norm_nonneg _) (norm_nonneg _),?_⟩
  intro d J hJ heJ
  let s := ConicalCommonFixedGauge.system p a center B hB hcontrast ha hsep i R T k b hR0 hRT hk hb hfreq hR hai d J hJ heJ
  let t := ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep i i R T k b hR0 hk hb hfreq hR hT hai
  let F := CommonTotalError.errorField p a center B hB hcontrast ha hsep i R T k hKR (hT i) d
  have he (j : Fin 3) : ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate s j x-totalCoordinate t j x = physicalCoordinate F j (x+center i) := by
    have hf := (ae_restrict_iff' (UnionFreeRunge.balls_compact center a).measurableSet).mp
      (CommonTotalErrorLocal.totalError_ae p a center ha B hB hcontrast hsep i R T k hKR hR (hT i) d j)
    have hshift := (measurePreserving_add_right (volume : Measure Space) (center i)).quasiMeasurePreserving.ae hf
    have hb0 := ConicalCommonPairing.tipCoordinate_actual p a center B hB hcontrast ha hsep i R T k b hb hR hT j
    filter_upwards [hshift, ConicalCommonFixedGauge.system_actual p a center B hB hcontrast ha hsep
      i R T k b hR0 hRT hk hb hfreq hR hai d J hJ heJ j,
      ConicalCommonResponse.tipSystem_actual p a center B hB hcontrast ha hsep
        i i R T k b hR0 hk hb hfreq hR hT hai j, hb0,
      StaticBallTranslation.scalar_ae (-center i) (physicalCoordinate (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) j)] with x hf hsyst ht hb0 htrans hx
    have hm : x+center i ∈ UnionFreeRunge.balls center a := by
      apply mem_iUnion.mpr
      refine ⟨i,?_⟩
      have hn : ‖x‖ < b := by simpa using hx
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_right] using (hn.trans hb).le
    dsimp only [s,t,F]
    rw [hsyst hx,ht hx]
    have hbase := hb0 hx
    have herr := hf hm
    change (ConicalCommonTipConvergence.tipCoordinate p a center B hB hcontrast ha hsep i j R T k : Space → ℂ) x = _ at htrans
    simp only [sub_neg_eq_add] at htrans
    rw [← htrans,hbase] at herr
    simpa only [add_comm] using herr.symm
  have hp := pair_difference (p i) b s t (center i) F ζ hζ hc hs he
  rw [hp]
  have hbound := (P.le_opNorm F).trans (mul_le_mul_of_nonneg_left
    (CommonTotalError.errorField_bound p a center B hB hcontrast ha hsep i R T k hKR (hT i) d) (norm_nonneg P))
  dsimp only [P,V,D,F] at *
  convert hbound using 1
  all_goals ring
end OQ14.CommonTotalPairStability
#print axioms OQ14.CommonTotalPairStability.pairMap_apply
#print axioms OQ14.CommonTotalPairStability.pair_difference


#print axioms OQ14.CommonTotalPairStability.uniform_bound



