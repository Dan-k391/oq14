import ConicalCommonTipConvergence

/-! Actual common response equals its centered projection system in the local material ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonPairing
open MeasureTheory Set Metric Filter OQ14.NewtonL2 OQ14.WeakGreen
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

omit [DecidableEq ι] in
theorem tipCoordinate_actual (i : ι) (R T k b : ℝ) (hb : b < a i)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T) (j : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalCommonTipConvergence.tipCoordinate p a center B hB hcontrast ha hsep i j R T k x =
        ConicalCommonResponse.electric p a center B hB hcontrast ha hsep i R T k (center i + x) j := by
  have he := (ae_restrict_iff' measurableSet_closedBall).mp
    (ConicalCommonResponse.field_ae p a center B hB hcontrast ha hsep i R T k hR hT j)
  have ht := (measurePreserving_add_right (volume : Measure Space) (center i)).quasiMeasurePreserving.ae he
  filter_upwards [StaticBallTranslation.scalar_ae (-center i)
    (physicalCoordinate (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) j), ht] with x hc hf hx
  have hm : x + center i ∈ ConicalCommonMaterial.materialBall a center i := by
    have hn : ‖x‖ < b := by simpa using hx
    simp only [ConicalCommonMaterial.materialBall, mem_closedBall, dist_eq_norm]
    simpa only [add_sub_cancel_right] using (hn.trans hb).le
  have hmem := hR i (ConicalCommonMaterial.material_subset_outer p a center ha i hm)
  change StaticBallTranslation.scalar (-center i) _ x = _
  rw [hc]
  have hf' := hf hmem
  simpa only [sub_neg_eq_add, add_comm] using hf'

theorem totalPair_eq (i : ι) (R T k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b < a i)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (hT : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b) :
    ConicalLocalStability.totalPair (ConicalCommonResponse.tipSystem p a center B hB hcontrast ha hsep
      i i R T k b hR0 hk hb hfreq hR hT hai) ζ hζ hc =
    ConicalCommonTipConvergence.tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc := by
  unfold ConicalLocalStability.totalPair ConicalCommonTipConvergence.tipPair
  apply Finset.sum_congr rfl
  intro j hj
  rw [scalarProduct_integral, scalarProduct_integral]
  apply integral_congr_ae
  filter_upwards [ConicalCommonResponse.tipSystem_actual p a center B hB hcontrast ha hsep
      i i R T k b hR0 hk hb hfreq hR hT hai j,
    tipCoordinate_actual p a center B hB hcontrast ha hsep i R T k b hb hR hT j,
    ConicalTangentialDivergence.tangentFieldL2_ae _ _ _ (p i).eigenvalue_bounds
      (p i).contrast_nonnegative (p i).threshold_pos (p i).threshold_lt_one ζ hζ hc j] with x hsyst htip ht
  by_cases hx : x ∈ ball (0 : Space) b
  · rw [hsyst hx, htip hx]
  · have hz : ζ ‖x‖ = 0 := image_eq_zero_of_nmem_tsupport (fun h => hx (by
      simpa only [mem_ball, dist_zero_right] using (hs h).2))
    change ConicalAnnularCoefficient.testCoordinate (p i) ζ hζ hc j x = _ at ht
    rw [ht]
    simp [ConicalTangentialDivergence.tangentField, hz]

end OQ14.ConicalCommonPairing
#print axioms OQ14.ConicalCommonPairing.tipCoordinate_actual
#print axioms OQ14.ConicalCommonPairing.totalPair_eq
