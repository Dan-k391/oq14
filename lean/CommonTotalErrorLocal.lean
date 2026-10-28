import CommonTotalError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.CommonTotalErrorLocal
open MeasureTheory Set Metric Filter OQ14.NewtonL2 OQ14.UnionFreeRunge
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)

omit [DecidableEq ι] in
theorem incidentError_ae (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) (d : Input) (j : Fin 3) :
    physicalCoordinate (UnionMaterialTransfer.vector (balls center a) (balls_compact center a).measurableSet
      (ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR hT d)) j =ᵐ[volume.restrict (balls center a)]
      fun x => (FiniteAngularHerglotz.incident k d).E x j - physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k) j x := by
  have hK := (balls_compact center a).measurableSet
  filter_upwards [ae_restrict_of_ae (UnionMaterialTransfer.vector_ae (balls center a) hK
      (ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR hT d) j),
    Lp.coeFn_add (UnionFiniteAngularRunge.incident k R (balls center a) hKR d j)
      (ConicalCommonErrorNorm.target p a center ha i R T k hKR hT j),
    UnionFiniteAngularRunge.incident_ae k R (balls center a) hKR d j,
    CommonUnionTarget.target_negative_incident p a center ha i R T k hKR hT j,
    ae_restrict_mem hK] with x hv hadd hi ht hx
  rw [hv,indicator_of_mem hx]
  change (UnionFiniteAngularRunge.incident k R (balls center a) hKR d j +
    ConicalCommonErrorNorm.target p a center ha i R T k hKR hT j) x = _
  rw [hadd]
  change (ConicalCommonErrorNorm.target p a center ha i R T k hKR hT j : Space → ℂ) x = _ at ht
  simp only [Pi.add_apply,hi,ht,sub_eq_add_neg]
theorem totalError_ae (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j))
    (i : ι) (R T k : ℝ) (hKR : balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T) (d : Input) (j : Fin 3) :
    physicalCoordinate (CommonTotalError.errorField p a center B hB hcontrast ha hsep i R T k hKR hT d) j
      =ᵐ[volume.restrict (balls center a)] fun x =>
        ConicalCommonEntire.electric p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d) x j -
          physicalCoordinate (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) j x := by
  let K := balls center a
  let c := ConicalCommonBaseline.common p a center B hB hcontrast ha hsep
  let u := ConicalCommonEntire.solution p a center B hB hcontrast ha hsep R k (FiniteAngularHerglotz.incident k d)
  let v := ConicalCommonDynamic.solution p a center B hB hcontrast ha hsep i R T k
  let D := newtonOperator + DynamicConvolution.operator k (2*R)
  let E := UnionMaterialTransfer.vector K (balls_compact center a).measurableSet
    (ConicalCommonErrorNorm.errorVector p a center ha i R T k hKR hT d)
  let M := StaticCoefficient.sqrtMultiplier c u
  let N := StaticCoefficient.sqrtMultiplier c v
  have hc := ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR
  have hsc := (LocalVolumeResponse.electric_ae_on_ball k R R M (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc) (DynamicVolume.source_zero c u R hc)
    (StaticNewton.material_source_ae c u) j).filter_mono (ae_mono (Measure.restrict_mono_set volume hKR))
  have hsc' : physicalCoordinate (D M) j =ᵐ[volume.restrict K]
      fun x => FieldResponse.electric k M (DynamicVolume.source c u) x j := by
    simpa only [D,LocalVolumeResponse.localRepresentative,two_mul,ContinuousLinearMap.add_apply] using hsc
  have hinc := incidentError_ae p a center ha i R T k hKR hT d j
  have hdiff := ae_restrict_of_ae (s := K) (ConicalResponseLinear.source_sub_ae (D M) (D N)
    (fun j => physicalCoordinate (D M) j) (fun j => physicalCoordinate (D N) j)
    (fun _ => Filter.EventuallyEq.rfl) (fun _ => Filter.EventuallyEq.rfl) j)
  have hadd := ae_restrict_of_ae (s := K) (Lp.coeFn_add (physicalCoordinate E j) (physicalCoordinate (D (M-N)) j))
  have hbase := ae_restrict_of_ae (s := K) (Lp.coeFn_add (physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k) j)
    (physicalCoordinate (D N) j))
  filter_upwards [hinc,hsc',hdiff,hadd,hbase] with x hi hs hd had hb
  change physicalCoordinate (E+D (StaticCoefficient.sqrtMultiplier c
    (CommonTotalError.solutionDifference p a center B hB hcontrast ha hsep i R T k hKR d))) j x = _
  have hsol : CommonTotalError.solutionDifference p a center B hB hcontrast ha hsep i R T k hKR d = u-v := by
    unfold CommonTotalError.solutionDifference
    rw [← CommonIncidentSolutionBridge.solution_eq p a center B hB hcontrast ha hsep R k hKR hR d]
  rw [hsol,map_sub]
  have hcadd : physicalCoordinate (E+D (M-N)) j = physicalCoordinate E j + physicalCoordinate (D (M-N)) j := by
    simp [physicalCoordinate]
  rw [hcadd]
  change (physicalCoordinate E j + physicalCoordinate (D (M-N)) j) x = _
  rw [had]
  simp only [Pi.add_apply]
  have hDM : D (M-N) = D M-D N := map_sub _ _ _
  rw [hDM,hd,hi,hs]
  have hf : ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k =
      ConicalCommonDynamic.incident p a center i R T k + D N := by
    rfl
  rw [hf]
  have hcbase : physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k + D N) j =
      physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k) j + physicalCoordinate (D N) j := by simp [physicalCoordinate]
  rw [hcbase]
  change _ = _ - (physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k) j + physicalCoordinate (D N) j) x
  rw [hb]
  simp only [Pi.add_apply,ConicalCommonEntire.electric,MaterialField.total,MaterialField.scattered]
  ring
end OQ14.CommonTotalErrorLocal
#print axioms OQ14.CommonTotalErrorLocal.incidentError_ae


#print axioms OQ14.CommonTotalErrorLocal.totalError_ae



