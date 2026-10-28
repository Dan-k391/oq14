import ConicalCommonEntire

/-! Linear local singular coefficients for finite angular incident fields of one common material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonAngular
open MeasureTheory Set Metric Filter OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))
variable (l : ι) (R k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b ≤ a l)
  (hai : a l < (p l).cutoff.rIn)
  (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
  (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
  (hb0 : 0 < b) (hν : (p l).exponent < 1)

def system (c : Input) : ConicalProjectionData.System (p l) b :=
  ConicalCommonEntire.system p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR
    (FiniteAngularHerglotz.incident k c)

def fieldLinear : Input →ₗ[ℂ] ConicalRungeBall.BallL2 R :=
  (ConicalMaterialRunge.totalOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R).toLinearMap.comp
    (ConicalAngularCoefficient.restrictedLinear R k)

omit [DecidableEq ι] in
theorem system_total_ae (c : Input) (j : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalProjectionData.totalCoordinate (system p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR c) j x =
        fieldLinear p a center B hB hcontrast ha hsep R k c j (x + center l) := by
  have he := (ae_restrict_iff' measurableSet_closedBall).mp
    (ConicalMaterialRunge.total_ae (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R _ _
      (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR)
      (ConicalEntireGauge.restricted_ae R (FiniteAngularHerglotz.incident k c)) j)
  have ht := (measurePreserving_add_right (volume : Measure Space) (center l)).quasiMeasurePreserving.ae he
  filter_upwards [ConicalCommonEntire.system_actual p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR
    (FiniteAngularHerglotz.incident k c) j, ht] with x hs ht hx
  have hm : x + center l ∈ ConicalCommonMaterial.materialBall a center l := by
    have hn : ‖x‖ < b := by simpa using hx
    simp only [ConicalCommonMaterial.materialBall, mem_closedBall, dist_eq_norm]
    simpa only [add_sub_cancel_right] using (hn.trans_le hb).le
  have hmem := hR l (ConicalCommonMaterial.material_subset_outer p a center ha l hm)
  change _ = (ConicalMaterialRunge.totalOperator _ k R (ConicalEntireGauge.restricted R (FiniteAngularHerglotz.incident k c)) j) (x+center l)
  dsimp only [system]
  rw [hs hx]
  simpa only [add_comm] using (ht hmem).symm

def coefficient (c : Input) : ℂ :=
  ConicalIntrinsicCoefficient.coefficient (system p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR c)
    hb0 (hb.trans_lt hai) hν

omit [DecidableEq ι] in
theorem coefficient_add (c d : Input) :
    coefficient p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR hb0 hν (c+d) =
      coefficient p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR hb0 hν c +
        coefficient p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR hb0 hν d := by
  apply ConicalIntrinsicCoefficient.coefficient_add _ _ _ hb0 (hb.trans_lt hai) hν
  intro j
  have hl := map_add (fieldLinear p a center B hB hcontrast ha hsep R k) c d
  have hadd := (ae_restrict_iff' measurableSet_closedBall).mp (Lp.coeFn_add
    (fieldLinear p a center B hB hcontrast ha hsep R k c j) (fieldLinear p a center B hB hcontrast ha hsep R k d j))
  have ht := (measurePreserving_add_right (volume : Measure Space) (center l)).quasiMeasurePreserving.ae hadd
  filter_upwards [system_total_ae p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR (c+d) j,
    system_total_ae p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR c j,
    system_total_ae p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR d j,ht] with x hc hd he ht hx
  have hm : x + center l ∈ ConicalCommonMaterial.materialBall a center l := by
    have hn : ‖x‖ < b := by simpa using hx
    simp only [ConicalCommonMaterial.materialBall, mem_closedBall, dist_eq_norm]
    simpa only [add_sub_cancel_right] using (hn.trans_le hb).le
  have hmem := hR l (ConicalCommonMaterial.material_subset_outer p a center ha l hm)
  rw [hc hx, hd hx, he hx, hl]
  exact ht hmem

omit [DecidableEq ι] in
theorem coefficient_smul (z : ℂ) (c : Input) :
    coefficient p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR hb0 hν (z • c) =
      z * coefficient p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR hb0 hν c := by
  apply ConicalIntrinsicCoefficient.coefficient_scaled _ _ hb0 (hb.trans_lt hai) hν z
  intro j
  have hl := map_smul (fieldLinear p a center B hB hcontrast ha hsep R k) z c
  have hadd := (ae_restrict_iff' measurableSet_closedBall).mp (Lp.coeFn_smul z (fieldLinear p a center B hB hcontrast ha hsep R k c j))
  have ht := (measurePreserving_add_right (volume : Measure Space) (center l)).quasiMeasurePreserving.ae hadd
  filter_upwards [system_total_ae p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR (z • c) j,
    system_total_ae p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR c j,ht] with x hc hd ht hx
  have hm : x + center l ∈ ConicalCommonMaterial.materialBall a center l := by
    have hn : ‖x‖ < b := by simpa using hx
    simp only [ConicalCommonMaterial.materialBall, mem_closedBall, dist_eq_norm]
    simpa only [add_sub_cancel_right] using (hn.trans_le hb).le
  have hmem := hR l (ConicalCommonMaterial.material_subset_outer p a center ha l hm)
  rw [hc hx, hd hx, hl]
  exact ht hmem

def coefficientLinear : Input →ₗ[ℂ] ℂ where
  toFun := coefficient p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR hb0 hν
  map_add' := coefficient_add p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR hb0 hν
  map_smul' := coefficient_smul p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR hb0 hν

end OQ14.ConicalCommonAngular
#print axioms OQ14.ConicalCommonAngular.system_total_ae
#print axioms OQ14.ConicalCommonAngular.coefficient_add
#print axioms OQ14.ConicalCommonAngular.coefficient_smul
#print axioms OQ14.ConicalCommonAngular.coefficientLinear
