import ConicalSeparatedDynamic
import ElectricPotentialDecomposition

/-! Actual physical Maxwell fields from the separated material and source construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.ConicalSeparatedMaxwell
open MeasureTheory Set Metric OQ14.Maxwell OQ14.NewtonL2 OQ14.ConicalStaticVolume
  OQ14.ConicalSeparatedSource OQ14.ConicalSeparatedDynamic OQ14.DynamicSource
open scoped SchwartzMap
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

def totalSource (p : Data) (a k : ℝ) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier (material p a) (solution p a k)-ConicalSeparatedSource.forcing p a

def source (p : Data) (a k : ℝ) (i : Fin 3) (x : Space) : ℂ :=
  DynamicVolume.source (material p a) (solution p a k) i x-physicalSource p a i x

theorem source_ae (p : Data) (a k : ℝ) (i : Fin 3) :
    physicalCoordinate (totalSource p a k) i =ᵐ[volume] source p a k i := by
  simp only [totalSource,physicalCoordinate,map_sub]
  filter_upwards [Lp.coeFn_sub
    (physicalCoordinate (StaticCoefficient.sqrtMultiplier (material p a) (solution p a k)) i)
    (physicalCoordinate (ConicalSeparatedSource.forcing p a) i),
    StaticNewton.material_source_ae (material p a) (solution p a k) i,forcing_ae p a i] with x hsub hm hf
  change (physicalCoordinate (StaticCoefficient.sqrtMultiplier (material p a) (solution p a k)) i-
    physicalCoordinate (ConicalSeparatedSource.forcing p a) i) x=_
  rw [hsub]
  simp only [Pi.sub_apply,hm,hf,source,DynamicVolume.source]

theorem material_compact_outer (p : Data) (a : ℝ) (hai : a < p.cutoff.rIn)
    (x : Space) (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) :
    (material p a).value (VectorFourier.coordinateMap x)=0 :=
  material_compact p a x (fun hn => hx (closedBall_subset_closedBall (hai.trans p.cutoff.rIn_lt_rOut).le hn))

theorem source_zero_outer (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3)
    (x : Space) (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : source p a k i x=0 := by
  rw [source,DynamicVolume.source_zero (material p a) (solution p a k) p.cutoff.rOut
    (material_compact_outer p a hai) i x hx,
    ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le i x hx,sub_self]

theorem source_integrable (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    Integrable (source p a k i) :=
  (DynamicVolume.source_integrable (material p a) (solution p a k) p.cutoff.rOut (material_compact_outer p a hai) i).sub
    (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le i)

theorem source_compact (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    HasCompactSupport (source p a k i) :=
  HasCompactSupport.intro' (isCompact_closedBall (0 : Space) p.cutoff.rOut) isClosed_closedBall
    (source_zero_outer p a k hai i)

def electric (p : Data) (a k : ℝ) : Field := FieldResponse.electric k (totalSource p a k) (source p a k)
def magnetic (p : Data) (a k : ℝ) : Field := MagneticResponse.magnetic k (source p a k)

theorem field_ae (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    physicalCoordinate (field p a k) i =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => electric p a k x i := by
  let M := StaticCoefficient.sqrtMultiplier (material p a) (solution p a k)
  let F := ConicalSeparatedSource.forcing p a
  let A : VectorL2 →L[ℂ] VectorL2 := newtonOperator+DynamicConvolution.operator k (a+p.cutoff.rOut)
  let B : VectorL2 →L[ℂ] VectorL2 := newtonOperator+DynamicConvolution.operator k (2*a)
  have hsmall := LocalVolumeResponse.electric_ae_on_ball k a a M
    (DynamicVolume.source (material p a) (solution p a k))
    (DynamicVolume.source_integrable (material p a) _ a (material_compact p a))
    (DynamicVolume.source_zero (material p a) _ a (material_compact p a))
    (StaticNewton.material_source_ae (material p a) _) i
  have hlarge := LocalVolumeResponse.electric_ae_on_ball k a p.cutoff.rOut M
    (DynamicVolume.source (material p a) (solution p a k))
    (DynamicVolume.source_integrable (material p a) _ p.cutoff.rOut (material_compact_outer p a hai))
    (DynamicVolume.source_zero (material p a) _ p.cutoff.rOut (material_compact_outer p a hai))
    (StaticNewton.material_source_ae (material p a) _) i
  have hsmall' : physicalCoordinate (B M) i =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      fun x => FieldResponse.electric k M (DynamicVolume.source (material p a) (solution p a k)) x i := by
    simpa only [B,LocalVolumeResponse.localRepresentative,two_mul,ContinuousLinearMap.add_apply] using hsmall
  have hlarge' : physicalCoordinate (A M) i =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      fun x => FieldResponse.electric k M (DynamicVolume.source (material p a) (solution p a k)) x i := by
    simpa only [A,LocalVolumeResponse.localRepresentative,ContinuousLinearMap.add_apply] using hlarge
  let C := (ConicalBallRestriction.scalar a).comp (DynamicConvolution.component i)
  have hs : C (B M)=C (A M) := by
    apply Lp.ext
    filter_upwards [ConicalBallRestriction.scalarRestriction_ae a (physicalCoordinate (B M) i),
      ConicalBallRestriction.scalarRestriction_ae a (physicalCoordinate (A M) i),hsmall',hlarge'] with x hl hr hs hl'
    change ConicalBallRestriction.scalarRestriction a (physicalCoordinate (B M) i) x=
      ConicalBallRestriction.scalarRestriction a (physicalCoordinate (A M) i) x
    rw [hl,hr,hs,hl']
  have he := LocalVolumeResponse.electric_ae_on_ball k a p.cutoff.rOut (totalSource p a k)
    (source p a k) (source_integrable p a k hai) (source_zero_outer p a k hai) (source_ae p a k) i
  have hid : C (field p a k)=C (A (totalSource p a k)) := by
    change C (-A F+B M)=C (A (M-F))
    rw [map_add,map_neg,map_sub,map_sub,hs]
    abel
  have hlocal : physicalCoordinate (field p a k) i =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      physicalCoordinate (A (totalSource p a k)) i := by
    filter_upwards [ConicalBallRestriction.scalarRestriction_ae a (physicalCoordinate (field p a k) i),
      ConicalBallRestriction.scalarRestriction_ae a (physicalCoordinate (A (totalSource p a k)) i)] with x hl hr
    have hx := congrArg (fun f : ConicalRungeBall.ScalarBall a => f x) hid
    change ConicalBallRestriction.scalarRestriction a (physicalCoordinate (field p a k) i) x=
      ConicalBallRestriction.scalarRestriction a (physicalCoordinate (A (totalSource p a k)) i) x at hx
    rwa [hl,hr] at hx
  exact hlocal.trans he

theorem electric_memLp (p : Data) (a k R : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    MemLp (fun x => electric p a k x i) 2 (volume.restrict (closedBall (0 : Space) R)) :=
  LocalVolumeResponse.electric_memLp_ball k R p.cutoff.rOut (totalSource p a k) (source p a k)
    (source_integrable p a k hai) (source_zero_outer p a k hai) (source_ae p a k) i

theorem magnetic_memLp (p : Data) (a k R : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    MemLp (fun x => magnetic p a k x i) 2 (volume.restrict (closedBall (0 : Space) R)) :=
  MagneticLocal.magnetic_memLp_ball k R p.cutoff.rOut (totalSource p a k) (source p a k)
    (source_integrable p a k hai) (source_zero_outer p a k hai) (source_ae p a k) i

theorem material_spatial_inside (p : Data) (a : ℝ) (hai : a < p.cutoff.rIn) (x : Space)
    (hx : x ∈ closedBall (0 : Space) a) :
    (material p a).value (VectorFourier.coordinateMap x)=ConicalCapField.permittivity p.contrast p.threshold x-1 := by
  have hn : ‖x‖ ≤ a := by simpa only [mem_closedBall,dist_zero_right] using hx
  rw [material_eq_inside p a x hn,coefficient_spatial]
  have hout : x ∈ closedBall (0 : Space) p.cutoff.rOut :=
    closedBall_subset_closedBall (hai.trans p.cutoff.rIn_lt_rOut).le hx
  simp only [ConicalAnnularSource.dielectric,if_pos hout]

theorem material_relation (p : Data) (a k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a) (i : Fin 3) :
    DynamicVolume.source (material p a) (solution p a k) i =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      fun x => ((ConicalCapField.permittivity p.contrast p.threshold x-1 : ℝ) : ℂ)*electric p a k x i := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_square_ae (material p a) (field p a k))
  rw [field_weighted p a k ha hk] at hs
  filter_upwards [ae_restrict_of_ae hs,
    ae_restrict_of_ae (physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier (material p a) (solution p a k)) i),
    ae_restrict_of_ae (StaticNewton.material_source_ae (material p a) (solution p a k) i),
    ae_restrict_of_ae (physicalCoordinate_ae (field p a k) i),field_ae p a k hai i,
    ae_restrict_mem measurableSet_closedBall] with x hs hm hsrc hf he hx
  change (Real.sqrt ((material p a).value (VectorFourier.coordinateMap x)) : ℂ)*
    solution p a k (VectorFourier.coordinateMap x) i=_
  rw [← hsrc,hm,hs]
  change ((material p a).value (VectorFourier.coordinateMap x) : ℂ)*field p a k (VectorFourier.coordinateMap x) i=_
  rw [material_spatial_inside p a hai x hx,← hf,he]

theorem source_pairing_inner (p : Data) (a k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) a) :
    (∫ x, electric p a k x i*f.val x)+(∫ x, source p a k i x*f.val x)=
      ∫ x, (ConicalCapField.permittivity p.contrast p.threshold x : ℂ)*electric p a k x i*f.val x := by
  have hi : Integrable (fun x => electric p a k x i*f.val x) :=
    FieldResponse.electric_test_integrable k (totalSource p a k) (source p a k)
      (source_integrable p a k hai) (source_compact p a k hai) i f
  rw [← integral_add hi
    (PointSingularity.test_product_integrable _ _ (source_integrable p a k hai i).locallyIntegrable
      f.val.continuous f.property)]
  apply integral_congr_ae
  have hm := (ae_restrict_iff' measurableSet_closedBall).mp (material_relation p a k ha hai hk i)
  filter_upwards [hm] with x hx
  by_cases hz : f.val x=0
  · simp only [hz,mul_zero,add_zero]
  · have hin : x ∈ closedBall (0 : Space) a := ball_subset_closedBall (hf (subset_tsupport _ hz))
    rw [source,hx hin,ConicalSeparatedSource.source_zero_material p a hai i x hin,sub_zero]
    simp only [Complex.ofReal_sub,Complex.ofReal_one]
    ring

theorem maxwell_inner (p : Data) (a k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) a) :
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (electric p a k)) i f=
      Complex.I*(k : ℂ)*MaterialMaxwell.fieldPair (magnetic p a k) i f ∧
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (magnetic p a k)) i f=
      -(Complex.I*(k : ℂ))*(∫ x, (ConicalCapField.permittivity p.contrast p.threshold x : ℂ)*
        electric p a k x i*f.val x) := by
  constructor
  · exact MagneticResponse.electric_curl_pairing k (totalSource p a k) (source p a k)
      (source_integrable p a k hai) (source_compact p a k hai) (source_ae p a k) i f
  · have h := MagneticResponse.magnetic_curl_pairing k (totalSource p a k) (source p a k)
      (source_integrable p a k hai) (source_compact p a k hai) (source_ae p a k) i f
    change MagneticResponse.curlPair (MaterialMaxwell.fieldPair (magnetic p a k)) i f=
      -(Complex.I*(k : ℂ))*((∫ x, electric p a k x i*f.val x)+(∫ x, source p a k i x*f.val x)) at h
    rw [source_pairing_inner p a k ha hai hk i f hf] at h
    exact h

end OQ14.ConicalSeparatedMaxwell

#print axioms OQ14.ConicalSeparatedMaxwell.source_ae
#print axioms OQ14.ConicalSeparatedMaxwell.material_compact_outer
#print axioms OQ14.ConicalSeparatedMaxwell.source_zero_outer
#print axioms OQ14.ConicalSeparatedMaxwell.source_integrable
#print axioms OQ14.ConicalSeparatedMaxwell.source_compact
#print axioms OQ14.ConicalSeparatedMaxwell.field_ae
#print axioms OQ14.ConicalSeparatedMaxwell.electric_memLp
#print axioms OQ14.ConicalSeparatedMaxwell.magnetic_memLp

#print axioms OQ14.ConicalSeparatedMaxwell.material_spatial_inside
#print axioms OQ14.ConicalSeparatedMaxwell.material_relation
#print axioms OQ14.ConicalSeparatedMaxwell.source_pairing_inner
#print axioms OQ14.ConicalSeparatedMaxwell.maxwell_inner
