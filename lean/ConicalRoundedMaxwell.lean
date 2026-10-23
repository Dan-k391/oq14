import ConicalRoundedPeaks
import ConicalInnerMaxwell

/-! Literal Green fields and inner Maxwell equations for the explicit tip-rounded material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalRoundedMaxwell
open MeasureTheory Metric Set OQ14.Maxwell OQ14.NewtonL2 OQ14.ConicalStaticVolume
  OQ14.ConicalSpatialMaxwell OQ14.DynamicSource
open scoped SchwartzMap
abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2

def material (p : Data) (n : ℕ) := ConicalTipRounding.rounded (coefficient p) n
abbrev permittivity := ConicalRoundedPeaks.permittivity

def response (p : Data) (k : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  newtonOperator+DynamicConvolution.operator k (2*p.cutoff.rOut)

def solution (p : Data) (n : ℕ) (k : ℝ) : VectorL2 :=
  MaterialVolumeLimit.weightedSolution (material p n) k p.cutoff.rOut (ConicalDynamicVolume.incident p k)

def totalSource (p : Data) (n : ℕ) (k : ℝ) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier (material p n) (solution p n k)-annularSource p

abbrev field := ConicalRoundedPeaks.field

theorem material_compact (p : Data) (n : ℕ) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) :
    (material p n).value (VectorFourier.coordinateMap x)=0 :=
  ConicalTipRounding.conical_common_support p n x hx

theorem material_spatial (p : Data) (n : ℕ) (x : Space) :
    (material p n).value (VectorFourier.coordinateMap x)=permittivity p n x-1 := by
  unfold permittivity ConicalRoundedPeaks.permittivity material
  ring

theorem field_eq (p : Data) (n : ℕ) (k : ℝ) :
    field p n k=response p k (totalSource p n k) := by
  simp only [field,ConicalRoundedPeaks.field,MaterialVolumeLimit.volumeField,
    ConicalDynamicVolume.incident,ConicalDynamicVolume.response,solution,totalSource,response,map_sub,material]
  abel

theorem field_weighted (p : Data) (n : ℕ) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    StaticCoefficient.sqrtMultiplier (material p n) (field p n k)=solution p n k :=
  MaterialVolumeLimit.volumeField_weighted (material p n) k p.cutoff.rOut p.cutoff.rOut_pos.le hk _

def source (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) (x : Space) : ℂ :=
  DynamicVolume.source (material p n) (solution p n k) i x-annular p i x

theorem source_ae (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) :
    physicalCoordinate (totalSource p n k) i =ᵐ[volume] source p n k i := by
  simp only [totalSource,physicalCoordinate,map_sub]
  filter_upwards [Lp.coeFn_sub
    (physicalCoordinate (StaticCoefficient.sqrtMultiplier (material p n) (solution p n k)) i)
    (physicalCoordinate (annularSource p) i),
    StaticNewton.material_source_ae (material p n) (solution p n k) i,annularSource_ae p i] with x hs hm ha
  change (physicalCoordinate (StaticCoefficient.sqrtMultiplier (material p n) (solution p n k)) i-
    physicalCoordinate (annularSource p) i) x=_
  rw [hs]
  simp only [Pi.sub_apply,hm,ha,source,DynamicVolume.source,annular]

theorem source_zero_outer (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : source p n k i x=0 := by
  rw [source,DynamicVolume.source_zero (material p n) (solution p n k) p.cutoff.rOut
    (material_compact p n) i x hx,annular_zero_outer p i x hx,sub_self]

theorem source_integrable (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) : Integrable (source p n k i) :=
  (DynamicVolume.source_integrable (material p n) (solution p n k) p.cutoff.rOut (material_compact p n) i).sub
    (annular_integrable p i)

theorem source_compact (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) : HasCompactSupport (source p n k i) :=
  HasCompactSupport.intro' (isCompact_closedBall (0 : Space) p.cutoff.rOut) isClosed_closedBall
    (source_zero_outer p n k i)

def electric (p : Data) (n : ℕ) (k : ℝ) : Field := FieldResponse.electric k (totalSource p n k) (source p n k)
def magnetic (p : Data) (n : ℕ) (k : ℝ) : Field := MagneticResponse.magnetic k (source p n k)

theorem field_ae (p : Data) (n : ℕ) (k : ℝ) (i : Fin 3) :
    physicalCoordinate (field p n k) i =ᵐ[volume.restrict (closedBall (0 : Space) p.cutoff.rOut)]
      fun x => electric p n k x i := by
  have h := LocalVolumeResponse.electric_ae_on_ball k p.cutoff.rOut p.cutoff.rOut (totalSource p n k)
    (source p n k) (source_integrable p n k) (source_zero_outer p n k) (source_ae p n k) i
  rw [field_eq]
  simpa only [response,LocalVolumeResponse.localRepresentative,
    ContinuousLinearMap.add_apply,two_mul] using h

theorem electric_memLp (p : Data) (n : ℕ) (k R : ℝ) (i : Fin 3) :
    MemLp (fun x => electric p n k x i) 2 (volume.restrict (closedBall (0 : Space) R)) :=
  LocalVolumeResponse.electric_memLp_ball k R p.cutoff.rOut (totalSource p n k)
    (source p n k) (source_integrable p n k) (source_zero_outer p n k) (source_ae p n k) i

theorem magnetic_memLp (p : Data) (n : ℕ) (k R : ℝ) (i : Fin 3) :
    MemLp (fun x => magnetic p n k x i) 2 (volume.restrict (closedBall (0 : Space) R)) :=
  MagneticLocal.magnetic_memLp_ball k R p.cutoff.rOut (totalSource p n k)
    (source p n k) (source_integrable p n k) (source_zero_outer p n k) (source_ae p n k) i

theorem material_relation (p : Data) (n : ℕ) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut) (i : Fin 3) :
    DynamicVolume.source (material p n) (solution p n k) i =ᵐ[volume.restrict (closedBall (0 : Space) p.cutoff.rOut)]
      fun x => ((permittivity p n x-1 : ℝ) : ℂ)*electric p n k x i := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_square_ae (material p n) (field p n k))
  rw [field_weighted p n k hk] at hs
  filter_upwards [ae_restrict_of_ae hs,
    ae_restrict_of_ae (physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier (material p n) (solution p n k)) i),
    ae_restrict_of_ae (StaticNewton.material_source_ae (material p n) (solution p n k) i),
    ae_restrict_of_ae (physicalCoordinate_ae (field p n k) i),field_ae p n k i] with x hs hm hsrc hf he
  change (Real.sqrt ((material p n).value (VectorFourier.coordinateMap x)) : ℂ)*
    solution p n k (VectorFourier.coordinateMap x) i=_
  rw [← hsrc,hm,hs]
  change ((material p n).value (VectorFourier.coordinateMap x) : ℂ)*field p n k (VectorFourier.coordinateMap x) i=_
  rw [material_spatial,← hf,he]

theorem source_pairing_inner (p : Data) (n : ℕ) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) p.cutoff.rIn) :
    (∫ x, electric p n k x i*f.val x)+(∫ x, source p n k i x*f.val x)=
      ∫ x, (permittivity p n x : ℂ)*electric p n k x i*f.val x := by
  have hi : Integrable (fun x => electric p n k x i*f.val x) :=
    FieldResponse.electric_test_integrable k (totalSource p n k) (source p n k)
      (source_integrable p n k) (source_compact p n k) i f
  rw [← integral_add hi
    (PointSingularity.test_product_integrable _ _ (source_integrable p n k i).locallyIntegrable
      f.val.continuous f.property)]
  apply integral_congr_ae
  have hm := (ae_restrict_iff' measurableSet_closedBall).mp (material_relation p n k hk i)
  filter_upwards [hm] with x hx
  by_cases hz : f.val x=0
  · simp only [hz,mul_zero,add_zero]
  · have hin : x ∈ ball (0 : Space) p.cutoff.rIn := hf (subset_tsupport _ hz)
    have hout : x ∈ closedBall (0 : Space) p.cutoff.rOut :=
      closedBall_subset_closedBall p.cutoff.rIn_lt_rOut.le (ball_subset_closedBall hin)
    rw [source,hx hout,annular_zero_inner p i x hin,sub_zero]
    simp only [Complex.ofReal_sub,Complex.ofReal_one]
    ring

theorem maxwell_inner (p : Data) (n : ℕ) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p n) p.cutoff.rOut)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ ball (0 : Space) p.cutoff.rIn) :
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (electric p n k)) i f=
      Complex.I*(k : ℂ)*MaterialMaxwell.fieldPair (magnetic p n k) i f ∧
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (magnetic p n k)) i f=
      -(Complex.I*(k : ℂ))*(∫ x, (permittivity p n x : ℂ)*
        electric p n k x i*f.val x) := by
  constructor
  · exact MagneticResponse.electric_curl_pairing k (totalSource p n k) (source p n k)
      (source_integrable p n k) (source_compact p n k) (source_ae p n k) i f
  · have h := MagneticResponse.magnetic_curl_pairing k (totalSource p n k) (source p n k)
      (source_integrable p n k) (source_compact p n k) (source_ae p n k) i f
    change MagneticResponse.curlPair (MaterialMaxwell.fieldPair (magnetic p n k)) i f=
      -(Complex.I*(k : ℂ))*((∫ x, electric p n k x i*f.val x)+(∫ x, source p n k i x*f.val x)) at h
    rw [source_pairing_inner p n k hk i f hf] at h
    exact h

end OQ14.ConicalRoundedMaxwell

#print axioms OQ14.ConicalRoundedMaxwell.material_compact
#print axioms OQ14.ConicalRoundedMaxwell.material_spatial
#print axioms OQ14.ConicalRoundedMaxwell.field_eq
#print axioms OQ14.ConicalRoundedMaxwell.field_weighted
#print axioms OQ14.ConicalRoundedMaxwell.source_ae
#print axioms OQ14.ConicalRoundedMaxwell.source_zero_outer
#print axioms OQ14.ConicalRoundedMaxwell.source_integrable
#print axioms OQ14.ConicalRoundedMaxwell.source_compact
#print axioms OQ14.ConicalRoundedMaxwell.field_ae
#print axioms OQ14.ConicalRoundedMaxwell.electric_memLp
#print axioms OQ14.ConicalRoundedMaxwell.magnetic_memLp
#print axioms OQ14.ConicalRoundedMaxwell.material_relation
#print axioms OQ14.ConicalRoundedMaxwell.source_pairing_inner
#print axioms OQ14.ConicalRoundedMaxwell.maxwell_inner
