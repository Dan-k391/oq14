import ConicalDynamicVolume
import MaterialField
import MagneticLocal
import MaterialMaxwell

/-! Actual spatial Green fields for the conical volume inverse and their inner Maxwell equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalSpatialMaxwell
open MeasureTheory Metric Set OQ14.Maxwell OQ14.NewtonL2 OQ14.ConicalStaticVolume
  OQ14.ConicalDynamicVolume OQ14.ConicalComplexLocalization OQ14.DynamicSource
open scoped SchwartzMap

abbrev Space := FourierL2.Space

def annular (p : Data) (i : Fin 3) (x : Space) : ℂ :=
  complexify (ConicalAnnularSource.forcing p.cutoff p.exponent p.eigenvalue p.contrast p.threshold) x i

theorem annular_zero_outer (p : Data) (i : Fin 3) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : annular p i x=0 := by
  simp only [annular,complexify,ConicalAnnularSource.forcing_zero_outer _ _ _ _ _ x hx,
    PiLp.zero_apply,Complex.ofReal_zero]

theorem annular_zero_inner (p : Data) (i : Fin 3) (x : Space)
    (hx : x ∈ ball (0 : Space) p.cutoff.rIn) : annular p i x=0 := by
  simp only [annular,complexify,ConicalAnnularSource.forcing_zero_inner _ _ _ _ _ x hx,
    PiLp.zero_apply,Complex.ofReal_zero]

theorem annular_integrable (p : Data) (i : Fin 3) : Integrable (annular p i) := by
  have hi : Integrable (physicalCoordinate (annularSource p) i : Space → ℂ) := by
    apply NewtonL1L2.compact_supported_integrable _ (closedBall 0 p.cutoff.rOut) (isCompact_closedBall _ _)
    filter_upwards [annularSource_ae p i] with x hx
    intro hn
    exact hx.trans (annular_zero_outer p i x hn)
  exact hi.congr (annularSource_ae p i)

def source (p : Data) (k : ℝ) (i : Fin 3) (x : Space) : ℂ :=
  DynamicVolume.source (coefficient p) (solution p k) i x-annular p i x

theorem source_ae (p : Data) (k : ℝ) (i : Fin 3) :
    physicalCoordinate (totalSource p k) i =ᵐ[volume] source p k i := by
  simp only [totalSource,physicalCoordinate,map_sub]
  filter_upwards [Lp.coeFn_sub
    (physicalCoordinate (StaticCoefficient.sqrtMultiplier (coefficient p) (solution p k)) i)
    (physicalCoordinate (annularSource p) i),
    StaticNewton.material_source_ae (coefficient p) (solution p k) i,annularSource_ae p i] with x hs hm ha
  change (physicalCoordinate (StaticCoefficient.sqrtMultiplier (coefficient p) (solution p k)) i-
    physicalCoordinate (annularSource p) i) x=_
  rw [hs]
  simp only [Pi.sub_apply,hm,ha,source,DynamicVolume.source,annular]

theorem source_zero_outer (p : Data) (k : ℝ) (i : Fin 3) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : source p k i x=0 := by
  rw [source,DynamicVolume.source_zero (coefficient p) (solution p k) p.cutoff.rOut
    (coefficient_compact p) i x hx,annular_zero_outer p i x hx,sub_self]

theorem source_integrable (p : Data) (k : ℝ) (i : Fin 3) : Integrable (source p k i) :=
  (DynamicVolume.source_integrable (coefficient p) (solution p k) p.cutoff.rOut (coefficient_compact p) i).sub
    (annular_integrable p i)

theorem source_compact (p : Data) (k : ℝ) (i : Fin 3) : HasCompactSupport (source p k i) :=
  HasCompactSupport.intro' (isCompact_closedBall (0 : Space) p.cutoff.rOut) isClosed_closedBall
    (source_zero_outer p k i)

def electric (p : Data) (k : ℝ) : Field := FieldResponse.electric k (totalSource p k) (source p k)
def magnetic (p : Data) (k : ℝ) : Field := MagneticResponse.magnetic k (source p k)

theorem field_ae (p : Data) (k : ℝ) (i : Fin 3) :
    physicalCoordinate (field p k) i =ᵐ[volume.restrict (closedBall (0 : Space) p.cutoff.rOut)]
      fun x => electric p k x i := by
  have h := LocalVolumeResponse.electric_ae_on_ball k p.cutoff.rOut p.cutoff.rOut (totalSource p k)
    (source p k) (source_integrable p k) (source_zero_outer p k) (source_ae p k) i
  simpa only [field,ConicalDynamicVolume.response,LocalVolumeResponse.localRepresentative,
    ContinuousLinearMap.add_apply,two_mul] using h

theorem electric_memLp (p : Data) (k R : ℝ) (i : Fin 3) :
    MemLp (fun x => electric p k x i) 2 (volume.restrict (closedBall (0 : Space) R)) :=
  LocalVolumeResponse.electric_memLp_ball k R p.cutoff.rOut (totalSource p k)
    (source p k) (source_integrable p k) (source_zero_outer p k) (source_ae p k) i

theorem magnetic_memLp (p : Data) (k R : ℝ) (i : Fin 3) :
    MemLp (fun x => magnetic p k x i) 2 (volume.restrict (closedBall (0 : Space) R)) :=
  MagneticLocal.magnetic_memLp_ball k R p.cutoff.rOut (totalSource p k)
    (source p k) (source_integrable p k) (source_zero_outer p k) (source_ae p k) i

theorem material_relation (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) (i : Fin 3) :
    DynamicVolume.source (coefficient p) (solution p k) i =ᵐ[volume.restrict (closedBall (0 : Space) p.cutoff.rOut)]
      fun x => ((ConicalAnnularSource.dielectric p.cutoff p.contrast p.threshold x-1 : ℝ) : ℂ)*electric p k x i := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_square_ae (coefficient p) (field p k))
  rw [field_weighted p k hk] at hs
  filter_upwards [ae_restrict_of_ae hs,
    ae_restrict_of_ae (physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier (coefficient p) (solution p k)) i),
    ae_restrict_of_ae (StaticNewton.material_source_ae (coefficient p) (solution p k) i),
    ae_restrict_of_ae (physicalCoordinate_ae (field p k) i),field_ae p k i] with x hs hm hsrc hf he
  change (Real.sqrt ((coefficient p).value (VectorFourier.coordinateMap x)) : ℂ)*
    solution p k (VectorFourier.coordinateMap x) i=_
  rw [← hsrc,hm,hs]
  change ((coefficient p).value (VectorFourier.coordinateMap x) : ℂ)*field p k (VectorFourier.coordinateMap x) i=_
  rw [coefficient_spatial,← hf,he]

theorem source_pairing_inner (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) p.cutoff.rIn) :
    (∫ x, electric p k x i*f.val x)+(∫ x, source p k i x*f.val x)=
      ∫ x, (ConicalCapField.permittivity p.contrast p.threshold x : ℂ)*electric p k x i*f.val x := by
  have hi : Integrable (fun x => electric p k x i*f.val x) :=
    FieldResponse.electric_test_integrable k (totalSource p k) (source p k)
      (source_integrable p k) (source_compact p k) i f
  rw [← integral_add hi
    (PointSingularity.test_product_integrable _ _ (source_integrable p k i).locallyIntegrable
      f.val.continuous f.property)]
  apply integral_congr_ae
  have hm := (ae_restrict_iff' measurableSet_closedBall).mp (material_relation p k hk i)
  filter_upwards [hm] with x hx
  by_cases hz : f.val x=0
  · simp only [hz,mul_zero,add_zero]
  · have hin : x ∈ ball (0 : Space) p.cutoff.rIn := hf (subset_tsupport _ hz)
    have hout : x ∈ closedBall (0 : Space) p.cutoff.rOut :=
      closedBall_subset_closedBall p.cutoff.rIn_lt_rOut.le (ball_subset_closedBall hin)
    rw [source,hx hout,annular_zero_inner p i x hin,sub_zero]
    simp only [ConicalAnnularSource.dielectric,if_pos hout,Complex.ofReal_sub,Complex.ofReal_one]
    ring

theorem maxwell_inner (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) p.cutoff.rIn) :
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (electric p k)) i f=
      Complex.I*(k : ℂ)*MaterialMaxwell.fieldPair (magnetic p k) i f ∧
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (magnetic p k)) i f=
      -(Complex.I*(k : ℂ))*(∫ x, (ConicalCapField.permittivity p.contrast p.threshold x : ℂ)*
        electric p k x i*f.val x) := by
  constructor
  · exact MagneticResponse.electric_curl_pairing k (totalSource p k) (source p k)
      (source_integrable p k) (source_compact p k) (source_ae p k) i f
  · have h := MagneticResponse.magnetic_curl_pairing k (totalSource p k) (source p k)
      (source_integrable p k) (source_compact p k) (source_ae p k) i f
    change MagneticResponse.curlPair (MaterialMaxwell.fieldPair (magnetic p k)) i f=
      -(Complex.I*(k : ℂ))*((∫ x, electric p k x i*f.val x)+(∫ x, source p k i x*f.val x)) at h
    rw [source_pairing_inner p k hk i f hf] at h
    exact h

end OQ14.ConicalSpatialMaxwell

#print axioms OQ14.ConicalSpatialMaxwell.annular_zero_outer
#print axioms OQ14.ConicalSpatialMaxwell.annular_zero_inner
#print axioms OQ14.ConicalSpatialMaxwell.annular_integrable
#print axioms OQ14.ConicalSpatialMaxwell.source_ae
#print axioms OQ14.ConicalSpatialMaxwell.source_zero_outer
#print axioms OQ14.ConicalSpatialMaxwell.source_integrable
#print axioms OQ14.ConicalSpatialMaxwell.source_compact
#print axioms OQ14.ConicalSpatialMaxwell.field_ae
#print axioms OQ14.ConicalSpatialMaxwell.electric_memLp
#print axioms OQ14.ConicalSpatialMaxwell.magnetic_memLp
#print axioms OQ14.ConicalSpatialMaxwell.material_relation
#print axioms OQ14.ConicalSpatialMaxwell.source_pairing_inner
#print axioms OQ14.ConicalSpatialMaxwell.maxwell_inner
