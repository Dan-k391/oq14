import ConicalSchwartzLocalization
import WeakPotentialProjection
import StaticBallNewton
import StaticNewton

/-! The actual localized conical field solves its static material volume equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalStaticVolume
open MeasureTheory Metric Set OQ14.NewtonL2 OQ14.ConicalCutoffGradient
  OQ14.ConicalCutoffCurl OQ14.ConicalAnnularSource OQ14.ConicalComplexLocalization
open scoped SchwartzMap

abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2

structure Data where
  cutoff : ContDiffBump (0 : Space)
  exponent : ℝ
  eigenvalue : ℝ
  contrast : ℝ
  threshold : ℝ
  exponent_pos : 0 < exponent
  eigenvalue_bounds : eigenvalue ∈ Icc (0 : ℝ) 2
  contrast_nonnegative : 0 ≤ contrast
  threshold_pos : 0 < threshold
  threshold_lt_one : threshold < 1
  angular_root : CapAngularShooting.determinant contrast threshold eigenvalue=0
  separation : exponent*(exponent+1)=eigenvalue

def potential (p : Data) : FourierL2.ScalarL2 :=
  (cutPotential_memLp_complex p.cutoff p.exponent p.eigenvalue p.threshold
    p.exponent_pos.le p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one).toLp
      (fun x => (cutPotential p.cutoff p.exponent p.eigenvalue p.threshold x : ℂ))

def electric (p : Data) : VectorL2 :=
  StaticBallNewton.fromComponents (fun i =>
    (cutElectric_memLp_complex p.cutoff p.exponent p.eigenvalue p.threshold
      p.exponent_pos.le p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i).toLp
        (fun x => complexify (cutElectric p.cutoff p.exponent p.eigenvalue p.threshold) x i))

def displacement (p : Data) : VectorL2 :=
  StaticBallNewton.fromComponents (fun i =>
    (cutCurl_memLp_complex p.cutoff p.exponent p.eigenvalue p.contrast p.threshold
      p.exponent_pos.le p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i).toLp
        (fun x => complexify (cutCurl p.cutoff p.exponent p.eigenvalue p.contrast p.threshold) x i))

def annularSource (p : Data) : VectorL2 :=
  StaticBallNewton.fromComponents (fun i =>
    (forcing_memLp_complex p.cutoff p.exponent p.eigenvalue p.contrast p.threshold
      p.exponent_pos.le p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i).toLp
        (fun x => complexify (forcing p.cutoff p.exponent p.eigenvalue p.contrast p.threshold) x i))

theorem potential_ae (p : Data) : potential p =ᵐ[volume]
    fun x => (cutPotential p.cutoff p.exponent p.eigenvalue p.threshold x : ℂ) :=
  (cutPotential_memLp_complex p.cutoff p.exponent p.eigenvalue p.threshold
    p.exponent_pos.le p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one).coeFn_toLp

theorem electric_ae (p : Data) (i : Fin 3) : physicalCoordinate (electric p) i =ᵐ[volume]
    fun x => complexify (cutElectric p.cutoff p.exponent p.eigenvalue p.threshold) x i := by
  rw [electric,StaticBallNewton.physicalCoordinate_fromComponents]
  exact MemLp.coeFn_toLp _

theorem displacement_ae (p : Data) (i : Fin 3) : physicalCoordinate (displacement p) i =ᵐ[volume]
    fun x => complexify (cutCurl p.cutoff p.exponent p.eigenvalue p.contrast p.threshold) x i := by
  rw [displacement,StaticBallNewton.physicalCoordinate_fromComponents]
  exact MemLp.coeFn_toLp _

theorem annularSource_ae (p : Data) (i : Fin 3) : physicalCoordinate (annularSource p) i =ᵐ[volume]
    fun x => complexify (forcing p.cutoff p.exponent p.eigenvalue p.contrast p.threshold) x i := by
  rw [annularSource,StaticBallNewton.physicalCoordinate_fromComponents]
  exact MemLp.coeFn_toLp _

def coefficient (p : Data) : StaticCoefficient.Coefficient where
  value x := dielectric p.cutoff p.contrast p.threshold (VectorFourier.coordinateMap.symm x)-1
  bound := p.contrast
  measurable := ((dielectric_measurable p.cutoff p.contrast p.threshold).comp
    VectorFourier.coordinateMap.symm.measurable).sub measurable_const
  nonnegative x := sub_nonneg.mpr (dielectric_bounds p.cutoff p.contrast p.threshold
    p.contrast_nonnegative (VectorFourier.coordinateMap.symm x)).1
  bounded x := by
    have h := (dielectric_bounds p.cutoff p.contrast p.threshold
      p.contrast_nonnegative (VectorFourier.coordinateMap.symm x)).2
    linarith

theorem coefficient_spatial (p : Data) (x : Space) :
    (coefficient p).value (VectorFourier.coordinateMap x)=dielectric p.cutoff p.contrast p.threshold x-1 := by
  simp only [coefficient,MeasurableEquiv.symm_apply_apply]

theorem coefficient_compact (p : Data) (x : Space) (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) :
    (coefficient p).value (VectorFourier.coordinateMap x)=0 := by
  rw [coefficient_spatial]
  simp only [dielectric,if_neg hx,sub_self]

def weightedElectric (p : Data) : VectorL2 := StaticCoefficient.sqrtMultiplier (coefficient p) (electric p)
def materialSource (p : Data) : VectorL2 := StaticCoefficient.sqrtMultiplier (coefficient p) (weightedElectric p)

theorem materialSource_ae (p : Data) (i : Fin 3) : physicalCoordinate (materialSource p) i =ᵐ[volume]
    fun x => ((dielectric p.cutoff p.contrast p.threshold x-1 : ℝ) : ℂ)*
      complexify (cutElectric p.cutoff p.exponent p.eigenvalue p.threshold) x i := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_square_ae (coefficient p) (electric p))
  filter_upwards [physicalCoordinate_ae (materialSource p) i,hs,
    physicalCoordinate_ae (electric p) i,electric_ae p i] with x hm hs he hv
  rw [hm]
  change (StaticCoefficient.sqrtMultiplier (coefficient p)
    (StaticCoefficient.sqrtMultiplier (coefficient p) (electric p))) (VectorFourier.coordinateMap x) i=_
  rw [hs]
  change ((coefficient p).value (VectorFourier.coordinateMap x) : ℂ)*electric p (VectorFourier.coordinateMap x) i=_
  rw [coefficient_spatial,← he,hv]

private theorem physical_ext (F G : VectorL2) (h : ∀ i, physicalCoordinate F i=physicalCoordinate G i) : F=G := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro i
  apply VectorFourier.scalarCoordinates.injective
  exact h i

theorem annularSource_identity (p : Data) : annularSource p=electric p+materialSource p-displacement p := by
  apply physical_ext
  intro i
  simp only [physicalCoordinate,map_sub,map_add]
  apply Lp.ext
  filter_upwards [annularSource_ae p i,electric_ae p i,materialSource_ae p i,displacement_ae p i,
    Lp.coeFn_sub (physicalCoordinate (electric p) i+physicalCoordinate (materialSource p) i)
      (physicalCoordinate (displacement p) i),
    Lp.coeFn_add (physicalCoordinate (electric p) i) (physicalCoordinate (materialSource p) i)]
      with x hf he hm hd hsub hadd
  change physicalCoordinate (annularSource p) i x=
    (physicalCoordinate (electric p) i+physicalCoordinate (materialSource p) i-physicalCoordinate (displacement p) i) x
  rw [hf,hsub]
  simp only [Pi.sub_apply]
  rw [hadd]
  simp only [Pi.sub_apply,Pi.add_apply,he,hm,hd,complexify,forcing,PiLp.sub_apply,PiLp.smul_apply,
    smul_eq_mul,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_one]
  ring

theorem electric_weak_gradient (p : Data) (i : Fin 3) (φ : 𝓢(Space,ℂ)) :
    (∫ x, physicalCoordinate (electric p) i x*φ x)=
      -(∫ x, potential p x*GradientProjection.pderivative i φ x) := by
  have hE : (∫ x, physicalCoordinate (electric p) i x*φ x)=
      ∫ x, complexify (cutElectric p.cutoff p.exponent p.eigenvalue p.threshold) x i*φ x := by
    apply integral_congr_ae
    filter_upwards [electric_ae p i] with x hx
    rw [hx]
  have hU : (∫ x, potential p x*GradientProjection.pderivative i φ x)=
      ∫ x, (cutPotential p.cutoff p.exponent p.eigenvalue p.threshold x : ℂ)*GradientProjection.pderivative i φ x := by
    apply integral_congr_ae
    filter_upwards [potential_ae p] with x hx
    rw [hx]
  rw [hE,hU]
  exact ConicalSchwartzLocalization.cut_weak_partial_schwartz p.cutoff p.exponent p.eigenvalue p.threshold
    p.exponent_pos p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i φ

theorem displacement_weak_divergence (p : Data) (φ : 𝓢(Space,ℂ)) :
    (∑ i : Fin 3, ∫ x, physicalCoordinate (displacement p) i x*GradientProjection.pderivative i φ x)=0 := by
  have he : (∑ i : Fin 3, ∫ x, physicalCoordinate (displacement p) i x*GradientProjection.pderivative i φ x)=
      ∑ i : Fin 3, ∫ x, complexify (cutCurl p.cutoff p.exponent p.eigenvalue p.contrast p.threshold) x i*
        GradientProjection.pderivative i φ x := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [displacement_ae p i] with x hx
    rw [hx]
  rw [he]
  exact ConicalSchwartzLocalization.cutCurl_weak_divergence_schwartz p.cutoff p.exponent p.eigenvalue
    p.contrast p.threshold p.exponent_pos p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos
    p.threshold_lt_one p.angular_root p.separation φ

theorem static_field_equation (p : Data) :
    electric p-newtonOperator (materialSource p)= -newtonOperator (annularSource p) := by
  rw [annularSource_identity]
  exact WeakPotentialProjection.static_forcing_identity (potential p) (electric p) (materialSource p)
    (displacement p) (electric_weak_gradient p) (displacement_weak_divergence p)

def staticIncident (p : Data) : VectorL2 := -newtonOperator (annularSource p)
def staticForcing (p : Data) : VectorL2 := StaticCoefficient.sqrtMultiplier (coefficient p) (staticIncident p)

theorem static_volume_equation (p : Data) :
    StaticNewton.volumeBlock (coefficient p) (weightedElectric p)=staticForcing p := by
  have h := congrArg (StaticCoefficient.sqrtMultiplier (coefficient p)) (static_field_equation p)
  simpa only [map_sub] using h

theorem static_inverse (p : Data) :
    Ring.inverse (StaticNewton.volumeBlock (coefficient p)) (staticForcing p)=weightedElectric p := by
  rw [← static_volume_equation]
  have he := Ring.inverse_mul_cancel (StaticNewton.volumeBlock (coefficient p))
    (StaticNewton.volumeBlock_isUnit (coefficient p))
  exact congrArg (fun T : VectorL2 →L[ℂ] VectorL2 => T (weightedElectric p)) he

end OQ14.ConicalStaticVolume

#print axioms OQ14.ConicalStaticVolume.potential_ae
#print axioms OQ14.ConicalStaticVolume.electric_ae
#print axioms OQ14.ConicalStaticVolume.displacement_ae
#print axioms OQ14.ConicalStaticVolume.annularSource_ae
#print axioms OQ14.ConicalStaticVolume.coefficient_spatial
#print axioms OQ14.ConicalStaticVolume.coefficient_compact
#print axioms OQ14.ConicalStaticVolume.materialSource_ae
#print axioms OQ14.ConicalStaticVolume.annularSource_identity
#print axioms OQ14.ConicalStaticVolume.electric_weak_gradient
#print axioms OQ14.ConicalStaticVolume.displacement_weak_divergence
#print axioms OQ14.ConicalStaticVolume.static_field_equation
#print axioms OQ14.ConicalStaticVolume.static_volume_equation
#print axioms OQ14.ConicalStaticVolume.static_inverse
