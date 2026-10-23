import ConicalStaticVolume
import ConicalSpatialMaxwell

/-! A smaller actual conical material ball and an actual forcing outside that entire ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalSeparatedSource
open MeasureTheory Set Metric OQ14.ConicalStaticVolume OQ14.NewtonL2
  OQ14.ConicalComplexLocalization OQ14.ConicalAnnularSource
open scoped SchwartzMap
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

def material (p : Data) (a : ℝ) : StaticCoefficient.Coefficient where
  value ξ := if ‖VectorFourier.coordinateMap.symm ξ‖ ≤ a then (coefficient p).value ξ else 0
  bound := p.contrast
  measurable := (coefficient p).measurable.piecewise
    (measurableSet_le (continuous_norm.measurable.comp VectorFourier.coordinateMap.symm.measurable) measurable_const)
    measurable_const
  nonnegative ξ := by split_ifs; exact (coefficient p).nonnegative ξ; exact le_rfl
  bounded ξ := by split_ifs; exact (coefficient p).bounded ξ; exact p.contrast_nonnegative

theorem material_eq_inside (p : Data) (a : ℝ) (x : Space) (hx : ‖x‖ ≤ a) :
    (material p a).value (VectorFourier.coordinateMap x)=(coefficient p).value (VectorFourier.coordinateMap x) := by
  simp only [material,MeasurableEquiv.symm_apply_apply,if_pos hx]

theorem material_compact (p : Data) (a : ℝ) (x : Space) (hx : x ∉ closedBall (0 : Space) a) :
    (material p a).value (VectorFourier.coordinateMap x)=0 := by
  have hn : ¬‖x‖ ≤ a := by simpa only [mem_closedBall,dist_zero_right] using hx
  simp only [material,MeasurableEquiv.symm_apply_apply,if_neg hn]

def weightedElectric (p : Data) (a : ℝ) : VectorL2 := StaticCoefficient.sqrtMultiplier (material p a) (electric p)
def materialSource (p : Data) (a : ℝ) : VectorL2 := StaticCoefficient.sqrtMultiplier (material p a) (weightedElectric p a)
def forcing (p : Data) (a : ℝ) : VectorL2 :=
  annularSource p+materialSource p a-ConicalStaticVolume.materialSource p

def physicalSource (p : Data) (a : ℝ) (i : Fin 3) (x : Space) : ℂ :=
  ConicalSpatialMaxwell.annular p i x+
    (((material p a).value (VectorFourier.coordinateMap x)-(coefficient p).value (VectorFourier.coordinateMap x) : ℝ) : ℂ)*
      complexify (ConicalCutoffGradient.cutElectric p.cutoff p.exponent p.eigenvalue p.threshold) x i

theorem materialSource_ae (p : Data) (a : ℝ) (i : Fin 3) :
    physicalCoordinate (materialSource p a) i =ᵐ[volume] fun x =>
      ((material p a).value (VectorFourier.coordinateMap x) : ℂ)*
        complexify (ConicalCutoffGradient.cutElectric p.cutoff p.exponent p.eigenvalue p.threshold) x i := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_square_ae (material p a) (electric p))
  filter_upwards [physicalCoordinate_ae (materialSource p a) i,hs,
    physicalCoordinate_ae (electric p) i,electric_ae p i] with x hm hs he hv
  rw [hm]
  change (StaticCoefficient.sqrtMultiplier (material p a)
    (StaticCoefficient.sqrtMultiplier (material p a) (electric p))) (VectorFourier.coordinateMap x) i=_
  rw [hs]
  change ((material p a).value (VectorFourier.coordinateMap x) : ℂ)*electric p (VectorFourier.coordinateMap x) i=_
  rw [← he,hv]

theorem forcing_identity (p : Data) (a : ℝ) : forcing p a=electric p+materialSource p a-displacement p := by
  rw [forcing,annularSource_identity]
  abel

theorem forcing_ae (p : Data) (a : ℝ) (i : Fin 3) :
    physicalCoordinate (forcing p a) i =ᵐ[volume] physicalSource p a i := by
  simp only [forcing,physicalCoordinate,map_sub,map_add]
  filter_upwards [Lp.coeFn_sub
    (physicalCoordinate (annularSource p) i+physicalCoordinate (materialSource p a) i)
    (physicalCoordinate (ConicalStaticVolume.materialSource p) i),
    Lp.coeFn_add (physicalCoordinate (annularSource p) i) (physicalCoordinate (materialSource p a) i),
    annularSource_ae p i,materialSource_ae p a i,ConicalStaticVolume.materialSource_ae p i] with x hsub hadd hf hm ho
  change (physicalCoordinate (annularSource p) i+physicalCoordinate (materialSource p a) i-
    physicalCoordinate (ConicalStaticVolume.materialSource p) i) x=_
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hadd]
  simp only [Pi.add_apply,hf,hm,ho,physicalSource,ConicalSpatialMaxwell.annular,
    coefficient_spatial,Complex.ofReal_sub]
  ring

theorem source_zero_material (p : Data) (a : ℝ) (ha : a < p.cutoff.rIn) (i : Fin 3) (x : Space)
    (hx : x ∈ closedBall (0 : Space) a) : physicalSource p a i x=0 := by
  have hn : ‖x‖ ≤ a := by simpa only [mem_closedBall,dist_zero_right] using hx
  have hi : x ∈ ball (0 : Space) p.cutoff.rIn := by
    simpa only [mem_ball,dist_zero_right] using hn.trans_lt ha
  simp only [physicalSource,material_eq_inside p a x hn,sub_self,Complex.ofReal_zero,zero_mul,
    ConicalSpatialMaxwell.annular_zero_inner p i x hi,add_zero]

theorem source_zero_outer (p : Data) (a : ℝ) (ha : a ≤ p.cutoff.rOut) (i : Fin 3) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : physicalSource p a i x=0 := by
  have hm : x ∉ closedBall (0 : Space) a := fun h => hx (closedBall_subset_closedBall ha h)
  simp only [physicalSource,material_compact p a x hm,coefficient_compact p x hx,sub_self,
    Complex.ofReal_zero,zero_mul,ConicalSpatialMaxwell.annular_zero_outer p i x hx,add_zero]

theorem source_integrable (p : Data) (a : ℝ) (ha : a ≤ p.cutoff.rOut) (i : Fin 3) :
    Integrable (physicalSource p a i) := by
  have hi : Integrable (physicalCoordinate (forcing p a) i : Space → ℂ) := by
    apply NewtonL1L2.compact_supported_integrable _ (closedBall 0 p.cutoff.rOut) (isCompact_closedBall _ _)
    filter_upwards [forcing_ae p a i] with x hx
    exact fun hn => hx.trans (source_zero_outer p a ha i x hn)
  exact hi.congr (forcing_ae p a i)

theorem source_compact (p : Data) (a : ℝ) (ha : a ≤ p.cutoff.rOut) (i : Fin 3) :
    HasCompactSupport (physicalSource p a i) :=
  HasCompactSupport.intro' (isCompact_closedBall (0 : Space) p.cutoff.rOut) isClosed_closedBall
    (source_zero_outer p a ha i)

theorem static_field_equation (p : Data) (a : ℝ) :
    electric p-newtonOperator (materialSource p a)= -newtonOperator (forcing p a) := by
  rw [forcing_identity]
  exact WeakPotentialProjection.static_forcing_identity (potential p) (electric p) (materialSource p a)
    (displacement p) (electric_weak_gradient p) (displacement_weak_divergence p)

def staticIncident (p : Data) (a : ℝ) : VectorL2 := -newtonOperator (forcing p a)
def staticForcing (p : Data) (a : ℝ) : VectorL2 := StaticCoefficient.sqrtMultiplier (material p a) (staticIncident p a)

theorem static_volume_equation (p : Data) (a : ℝ) :
    StaticNewton.volumeBlock (material p a) (weightedElectric p a)=staticForcing p a := by
  have h := congrArg (StaticCoefficient.sqrtMultiplier (material p a)) (static_field_equation p a)
  simpa only [map_sub] using h

theorem static_inverse (p : Data) (a : ℝ) :
    Ring.inverse (StaticNewton.volumeBlock (material p a)) (staticForcing p a)=weightedElectric p a := by
  rw [← static_volume_equation]
  have he := Ring.inverse_mul_cancel (StaticNewton.volumeBlock (material p a))
    (StaticNewton.volumeBlock_isUnit (material p a))
  exact congrArg (fun T : VectorL2 →L[ℂ] VectorL2 => T (weightedElectric p a)) he

end OQ14.ConicalSeparatedSource

#print axioms OQ14.ConicalSeparatedSource.material_eq_inside
#print axioms OQ14.ConicalSeparatedSource.material_compact
#print axioms OQ14.ConicalSeparatedSource.materialSource_ae
#print axioms OQ14.ConicalSeparatedSource.forcing_identity
#print axioms OQ14.ConicalSeparatedSource.forcing_ae
#print axioms OQ14.ConicalSeparatedSource.source_zero_material
#print axioms OQ14.ConicalSeparatedSource.source_zero_outer
#print axioms OQ14.ConicalSeparatedSource.source_integrable
#print axioms OQ14.ConicalSeparatedSource.source_compact
#print axioms OQ14.ConicalSeparatedSource.static_field_equation
#print axioms OQ14.ConicalSeparatedSource.static_volume_equation
#print axioms OQ14.ConicalSeparatedSource.static_inverse
