import CompactCommonMaterial
import StaticBallTranslation

/-! Translated actual separated sources and static baseline in the common material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonBaseline
open MeasureTheory Set Metric OQ14.NewtonL2
open scoped Topology SchwartzMap
abbrev Data := ConicalStaticVolume.Data
abbrev VectorL2 := VectorFourier.VectorL2

def translate (c : Space) (F : VectorL2) : VectorL2 :=
  StaticBallNewton.fromComponents (fun i => StaticBallTranslation.scalar c (physicalCoordinate F i))

theorem translate_coordinate (c : Space) (F : VectorL2) (i : Fin 3) :
    physicalCoordinate (translate c F) i = StaticBallTranslation.scalar c (physicalCoordinate F i) :=
  StaticBallNewton.physicalCoordinate_fromComponents _ _

theorem translate_coordinate_ae (c : Space) (F : VectorL2) (i : Fin 3) :
    physicalCoordinate (translate c F) i =ᵐ[volume] fun x => physicalCoordinate F i (x-c) := by
  rw [translate_coordinate]
  exact StaticBallTranslation.scalar_ae c _

theorem translate_ae (c : Space) (F : VectorL2) (i : Fin 3) (f : Space → ℂ)
    (hf : physicalCoordinate F i =ᵐ[volume] f) :
    physicalCoordinate (translate c F) i =ᵐ[volume] fun x => f (x-c) := by
  have h := (measurePreserving_add_right (volume : Measure Space) (-c)).quasiMeasurePreserving.ae hf
  exact (translate_coordinate_ae c F i).trans (by simpa only [sub_eq_add_neg] using h)

theorem translate_gradient (c : Space) (p : Data) (i : Fin 3) (φ : 𝓢(Space, ℂ)) :
    (∫ x, physicalCoordinate (translate c (ConicalStaticVolume.electric p)) i x * φ x) =
      -(∫ x, StaticBallTranslation.scalar c (ConicalStaticVolume.potential p) x *
        GradientProjection.pderivative i φ x) := by
  rw [translate_coordinate]
  exact StaticBallTranslation.translated_weak_derivative c _ _ i
    (ConicalStaticVolume.electric_weak_gradient p i) φ

theorem translate_divergence (c : Space) (p : Data) (φ : 𝓢(Space, ℂ)) :
    (∑ i : Fin 3, ∫ x, physicalCoordinate (translate c (ConicalStaticVolume.displacement p)) i x *
      GradientProjection.pderivative i φ x) = 0 := by
  simp only [translate_coordinate, StaticBallTranslation.scalar_pairing,
    ← NewtonConvolution.translate_pderivative]
  exact ConicalStaticVolume.displacement_weak_divergence p (NewtonConvolution.translate c φ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def common := ConicalCommonMaterial.coefficient p a center B hB hcontrast ha hsep

def electric (i : ι) : VectorL2 := translate (center i) (ConicalStaticVolume.electric (p i))
def potential (i : ι) := StaticBallTranslation.scalar (center i) (ConicalStaticVolume.potential (p i))
def displacement (i : ι) : VectorL2 := translate (center i) (ConicalStaticVolume.displacement (p i))
def weighted (i : ι) : VectorL2 := StaticCoefficient.sqrtMultiplier (common p a center B hB hcontrast ha hsep) (electric p center i)
def materialSource (i : ι) : VectorL2 := StaticCoefficient.sqrtMultiplier (common p a center B hB hcontrast ha hsep) (weighted p a center B hB hcontrast ha hsep i)
def forcing (i : ι) : VectorL2 := translate (center i) (ConicalSeparatedSource.forcing (p i) (a i))

omit [Fintype ι] [DecidableEq ι] in
theorem source_ae (i : ι) (t : Fin 3) :
    physicalCoordinate (forcing p a center i) t =ᵐ[volume] ConicalCommonMaterial.source p a center i t :=
  translate_ae _ _ _ _ (ConicalSeparatedSource.forcing_ae (p i) (a i) t)

theorem physical_ext (F G : VectorL2) (h : ∀ i, physicalCoordinate F i = physicalCoordinate G i) : F = G := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro i
  apply VectorFourier.scalarCoordinates.injective
  exact h i

omit [DecidableEq ι] in
theorem materialSource_eq (i : ι) :
    materialSource p a center B hB hcontrast ha hsep i =
      translate (center i) (ConicalSeparatedSource.materialSource (p i) (a i)) := by
  apply physical_ext
  intro t
  apply Lp.ext
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_square_ae (common p a center B hB hcontrast ha hsep) (electric p center i))
  filter_upwards [physicalCoordinate_ae (materialSource p a center B hB hcontrast ha hsep i) t,
    hs, physicalCoordinate_ae (electric p center i) t,
    translate_ae (center i) (ConicalStaticVolume.electric (p i)) t _ (ConicalStaticVolume.electric_ae (p i) t),
    translate_ae (center i) (ConicalSeparatedSource.materialSource (p i) (a i)) t _
      (ConicalSeparatedSource.materialSource_ae (p i) (a i) t)] with x hm hs he he' ht
  rw [hm]
  change (StaticCoefficient.sqrtMultiplier (common p a center B hB hcontrast ha hsep)
    (StaticCoefficient.sqrtMultiplier (common p a center B hB hcontrast ha hsep) (electric p center i)))
      (VectorFourier.coordinateMap x) t = _
  rw [hs]
  change ((common p a center B hB hcontrast ha hsep).value (VectorFourier.coordinateMap x) : ℂ) *
      electric p center i (VectorFourier.coordinateMap x) t = _
  change physicalCoordinate (electric p center i) t x = _ at he'
  rw [← he, he', ht]
  exact ConicalCommonMaterial.coefficient_mul_electric p a center B hB hcontrast ha hsep i x t

omit [DecidableEq ι] in
theorem forcing_identity (i : ι) : forcing p a center i =
    electric p center i + materialSource p a center B hB hcontrast ha hsep i - displacement p center i := by
  rw [materialSource_eq]
  apply physical_ext
  intro t
  change physicalCoordinate (translate (center i) (ConicalSeparatedSource.forcing (p i) (a i))) t = _
  rw [ConicalSeparatedSource.forcing_identity, translate_coordinate]
  have hadd (F G : VectorL2) : physicalCoordinate (F + G) t = physicalCoordinate F t + physicalCoordinate G t := by simp [physicalCoordinate]
  have hsub (F G : VectorL2) : physicalCoordinate (F - G) t = physicalCoordinate F t - physicalCoordinate G t := by simp [physicalCoordinate]
  simp only [hadd, hsub, map_add, map_sub, electric, displacement, translate_coordinate]

omit [DecidableEq ι] in
theorem static_field_equation (i : ι) :
    electric p center i - newtonOperator (materialSource p a center B hB hcontrast ha hsep i) =
      -newtonOperator (forcing p a center i) := by
  rw [forcing_identity]
  exact WeakPotentialProjection.static_forcing_identity (potential p center i) (electric p center i)
    (materialSource p a center B hB hcontrast ha hsep i) (displacement p center i)
    (translate_gradient (center i) (p i)) (translate_divergence (center i) (p i))

omit [DecidableEq ι] in
theorem static_volume_equation (i : ι) :
    StaticNewton.volumeBlock (common p a center B hB hcontrast ha hsep)
      (weighted p a center B hB hcontrast ha hsep i) =
      StaticCoefficient.sqrtMultiplier (common p a center B hB hcontrast ha hsep)
        (-newtonOperator (forcing p a center i)) := by
  have h := congrArg (StaticCoefficient.sqrtMultiplier (common p a center B hB hcontrast ha hsep))
    (static_field_equation p a center B hB hcontrast ha hsep i)
  simpa only [map_sub] using h

omit [DecidableEq ι] in
theorem static_inverse (i : ι) :
    Ring.inverse (StaticNewton.volumeBlock (common p a center B hB hcontrast ha hsep))
      (StaticCoefficient.sqrtMultiplier (common p a center B hB hcontrast ha hsep)
        (-newtonOperator (forcing p a center i))) = weighted p a center B hB hcontrast ha hsep i := by
  rw [← static_volume_equation]
  have he := Ring.inverse_mul_cancel _ (StaticNewton.volumeBlock_isUnit (common p a center B hB hcontrast ha hsep))
  exact congrArg (fun T : VectorL2 →L[ℂ] VectorL2 => T (weighted p a center B hB hcontrast ha hsep i)) he

omit [Fintype ι] [DecidableEq ι] in
theorem source_compact (i : ι) (t : Fin 3) (R : ℝ)
    (hR : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hai : a i ≤ (p i).cutoff.rOut) : HasCompactSupport (ConicalCommonMaterial.source p a center i t) :=
  HasCompactSupport.intro' (isCompact_closedBall (0 : Space) R) isClosed_closedBall
    (ConicalCommonMaterial.source_zero_global_outer p a center i t R hR · · hai)

omit [Fintype ι] [DecidableEq ι] in
theorem source_integrable (i : ι) (t : Fin 3) (R : ℝ)
    (hR : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hai : a i ≤ (p i).cutoff.rOut) : Integrable (ConicalCommonMaterial.source p a center i t) := by
  have hi : Integrable (physicalCoordinate (forcing p a center i) t : Space → ℂ) := by
    apply NewtonL1L2.compact_supported_integrable _ (closedBall 0 R) (isCompact_closedBall _ _)
    filter_upwards [source_ae p a center i t] with x hx
    exact fun hn => hx.trans (ConicalCommonMaterial.source_zero_global_outer p a center i t R hR x hn hai)
  exact hi.congr (source_ae p a center i t)

end OQ14.ConicalCommonBaseline

#print axioms OQ14.ConicalCommonBaseline.translate_coordinate
#print axioms OQ14.ConicalCommonBaseline.translate_coordinate_ae
#print axioms OQ14.ConicalCommonBaseline.translate_ae
#print axioms OQ14.ConicalCommonBaseline.translate_gradient
#print axioms OQ14.ConicalCommonBaseline.translate_divergence
#print axioms OQ14.ConicalCommonBaseline.source_ae
#print axioms OQ14.ConicalCommonBaseline.physical_ext
#print axioms OQ14.ConicalCommonBaseline.materialSource_eq
#print axioms OQ14.ConicalCommonBaseline.forcing_identity
#print axioms OQ14.ConicalCommonBaseline.static_field_equation
#print axioms OQ14.ConicalCommonBaseline.static_volume_equation
#print axioms OQ14.ConicalCommonBaseline.static_inverse
#print axioms OQ14.ConicalCommonBaseline.source_compact
#print axioms OQ14.ConicalCommonBaseline.source_integrable

