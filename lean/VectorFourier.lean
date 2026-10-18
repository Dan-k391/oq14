import FourierL2
import LongitudinalProjection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Actual vector Fourier transform and physical longitudinal projection

The coordinate change is proved volume preserving. Fourier acts componentwise
on genuine vector L2 through the actual scalar Plancherel equivalence.
The physical longitudinal projection is its conjugate of the verified symbol.
Identification with the Newton potential remains a separate statement.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.VectorFourier

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate FourierTransform SchwartzMap

abbrev Space := FourierL2.Space
abbrev Frequency := LongitudinalProjection.Frequency
abbrev Vector := LongitudinalProjection.Vector
abbrev VectorL2 := LongitudinalProjection.FrequencyL2
abbrev ScalarL2 := Lp ℂ 2 (volume : Measure Frequency)
abbrev ComponentL2 := PiLp 2 (fun _ : Fin 3 => ScalarL2)

def coordinateMap : Space ≃ᵐ Frequency := EuclideanSpace.measurableEquiv (Fin 3)

theorem coordinateMap_preserving : MeasurePreserving coordinateMap :=
  EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)

def scalarToEuclidean : ScalarL2 →ₗᵢ[ℂ] FourierL2.ScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ coordinateMap coordinateMap_preserving

def scalarFromEuclidean : FourierL2.ScalarL2 →ₗᵢ[ℂ] ScalarL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ coordinateMap.symm coordinateMap_preserving.symm

theorem scalarToFrom (f : FourierL2.ScalarL2) :
    scalarToEuclidean (scalarFromEuclidean f) = f := by
  apply Lp.ext
  have h := coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving f coordinateMap_preserving.symm)
  filter_upwards [Lp.coeFn_compMeasurePreserving (scalarFromEuclidean f)
    coordinateMap_preserving, h] with x hx hy
  change scalarToEuclidean (scalarFromEuclidean f) x = f x
  simpa only [Function.comp_apply, MeasurableEquiv.symm_apply_apply] using hx.trans hy

theorem scalarFromTo (f : ScalarL2) :
    scalarFromEuclidean (scalarToEuclidean f) = f := by
  apply Lp.ext
  have h := (MeasurePreserving.symm coordinateMap coordinateMap_preserving).quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving f coordinateMap_preserving)
  filter_upwards [Lp.coeFn_compMeasurePreserving (scalarToEuclidean f)
    coordinateMap_preserving.symm, h] with x hx hy
  change scalarFromEuclidean (scalarToEuclidean f) x = f x
  simpa only [Function.comp_apply, MeasurableEquiv.apply_symm_apply] using hx.trans hy

def scalarCoordinates : ScalarL2 ≃ₗᵢ[ℂ] FourierL2.ScalarL2 :=
  LinearIsometryEquiv.ofLinearIsometry scalarToEuclidean scalarFromEuclidean.toLinearMap
    (by ext1 f; exact scalarToFrom f) (by ext1 f; exact scalarFromTo f)

def scalarFourier : ScalarL2 ≃ₗᵢ[ℂ] ScalarL2 :=
  scalarCoordinates.trans (FourierL2.fourierEquiv.trans scalarCoordinates.symm)

theorem scalarCoordinates_symm (f : FourierL2.ScalarL2) :
    scalarCoordinates.symm f = scalarFromEuclidean f := rfl

def scalarEmbed (f : 𝓢(Space, ℂ)) : ScalarL2 :=
  scalarCoordinates.symm (FourierL2.embed f)

theorem scalarEmbed_ae (f : 𝓢(Space, ℂ)) :
    scalarEmbed f =ᵐ[volume] fun x => f (coordinateMap.symm x) := by
  have h := (MeasurePreserving.symm coordinateMap coordinateMap_preserving).quasiMeasurePreserving.ae
    (FourierL2.embed_ae f)
  filter_upwards [Lp.coeFn_compMeasurePreserving (FourierL2.embed f)
    (MeasurePreserving.symm coordinateMap coordinateMap_preserving), h] with x hx hy
  exact hx.trans hy

theorem scalarFourier_embed (f : 𝓢(Space, ℂ)) :
    scalarFourier (scalarEmbed f) = scalarEmbed (SchwartzMap.fourierTransformCLE ℂ f) := by
  simp only [scalarFourier, scalarEmbed, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, FourierL2.fourierEquiv_embed]

theorem scalarFourier_ae_integral (f : 𝓢(Space, ℂ)) :
    scalarFourier (scalarEmbed f) =ᵐ[volume] fun ξ => 𝓕 f (coordinateMap.symm ξ) := by
  rw [scalarFourier_embed]
  exact scalarEmbed_ae (SchwartzMap.fourierTransformCLE ℂ f)

def coordinate (i : Fin 3) : VectorL2 →L[ℂ] ScalarL2 :=
  (EuclideanSpace.proj i : Vector →L[ℂ] ℂ).compLpL 2 volume

theorem coordinate_ae (i : Fin 3) (f : VectorL2) :
    coordinate i f =ᵐ[volume] fun x => f x i :=
  (EuclideanSpace.proj i : Vector →L[ℂ] ℂ).coeFn_compLpL f

def componentsLinear : VectorL2 →ₗ[ℂ] ComponentL2 where
  toFun f := (WithLp.equiv 2 (Fin 3 → ScalarL2)).symm (fun i => coordinate i f)
  map_add' f g := by apply PiLp.ext; intro i; exact map_add (coordinate i) f g
  map_smul' c f := by apply PiLp.ext; intro i; exact map_smul (coordinate i) c f

theorem components_apply (f : VectorL2) (i : Fin 3) :
    componentsLinear f i = coordinate i f := rfl

theorem components_inner (f g : VectorL2) :
    ⟪componentsLinear f, componentsLinear g⟫_ℂ = ⟪f, g⟫_ℂ := by
  rw [PiLp.inner_apply, MeasureTheory.L2.inner_def]
  simp only [components_apply, MeasureTheory.L2.inner_def]
  rw [← integral_finset_sum _ (fun i _ => L2.integrable_inner (coordinate i f) (coordinate i g))]
  apply integral_congr_ae
  have hf : ∀ᵐ x ∂(volume : Measure Frequency), ∀ i : Fin 3,
      coordinate i f x = f x i := ae_all_iff.mpr (fun i => coordinate_ae i f)
  have hg : ∀ᵐ x ∂(volume : Measure Frequency), ∀ i : Fin 3,
      coordinate i g x = g x i := ae_all_iff.mpr (fun i => coordinate_ae i g)
  filter_upwards [hf, hg] with x hx hy
  simp only [hx, hy, PiLp.inner_apply]

theorem components_norm (f : VectorL2) : ‖componentsLinear f‖ = ‖f‖ := by
  have h := congrArg Complex.re (components_inner f f)
  have h1 : (⟪componentsLinear f, componentsLinear f⟫_ℂ).re = ‖componentsLinear f‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (componentsLinear f))
  have h2 : (⟪f, f⟫_ℂ).re = ‖f‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) f)
  rw [h1, h2] at h
  nlinarith [norm_nonneg (componentsLinear f), norm_nonneg f]

def componentsIsometry : VectorL2 →ₗᵢ[ℂ] ComponentL2 where
  toLinearMap := componentsLinear
  norm_map' := components_norm

def insertionValue (j : Fin 3) : ℂ →L[ℂ] Vector :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single j 1)

def insertion (j : Fin 3) : ScalarL2 →L[ℂ] VectorL2 :=
  (insertionValue j).compLpL 2 volume

theorem coordinate_insertion (i j : Fin 3) (f : ScalarL2) :
    coordinate i (insertion j f) = if i = j then f else 0 := by
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    apply Lp.ext
    filter_upwards [coordinate_ae i (insertion i f), (insertionValue i).coeFn_compLpL f]
      with x hx hy
    change insertion i f x = insertionValue i (f x) at hy
    rw [hx, hy]
    simp [insertionValue]
  · rw [if_neg hij]
    apply Lp.ext
    filter_upwards [coordinate_ae i (insertion j f), (insertionValue j).coeFn_compLpL f,
      Lp.coeFn_zero ℂ 2 (volume : Measure Frequency)] with x hx hy hz
    change insertion j f x = insertionValue j (f x) at hy
    rw [hx, hy, hz]
    simp [insertionValue, hij]

def assemble (v : ComponentL2) : VectorL2 := ∑ j : Fin 3, insertion j (v j)

theorem coordinate_assemble (i : Fin 3) (v : ComponentL2) :
    coordinate i (assemble v) = v i := by
  simp [assemble, map_sum, coordinate_insertion]

theorem components_surjective : Function.Surjective componentsIsometry := by
  intro v
  refine ⟨assemble v, ?_⟩
  apply PiLp.ext
  intro i
  exact coordinate_assemble i v

def components : VectorL2 ≃ₗᵢ[ℂ] ComponentL2 :=
  LinearIsometryEquiv.ofSurjective componentsIsometry components_surjective

theorem components_coordinate (f : VectorL2) (i : Fin 3) :
    components f i = coordinate i f := rfl

/-- The actual vector Fourier equivalence in Cartesian coordinates. -/
def fourier : VectorL2 ≃ₗᵢ[ℂ] VectorL2 :=
  components.trans
    ((LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 3 => scalarFourier)).trans components.symm)

theorem fourier_norm (f : VectorL2) : ‖fourier f‖ = ‖f‖ := fourier.norm_map f

theorem fourier_inner (f g : VectorL2) : ⟪fourier f, fourier g⟫_ℂ = ⟪f, g⟫_ℂ :=
  fourier.inner_map_map f g

theorem fourier_coordinate (f : VectorL2) (i : Fin 3) :
    coordinate i (fourier f) = scalarFourier (coordinate i f) := by
  change components (fourier f) i = scalarFourier (components f i)
  simp [fourier, LinearIsometryEquiv.piLpCongrRight_apply]

def schwartzVector (f : Fin 3 → 𝓢(Space, ℂ)) : VectorL2 :=
  components.symm ((WithLp.equiv 2 (Fin 3 → ScalarL2)).symm (fun i => scalarEmbed (f i)))

theorem coordinate_schwartzVector (f : Fin 3 → 𝓢(Space, ℂ)) (i : Fin 3) :
    coordinate i (schwartzVector f) = scalarEmbed (f i) := by
  change components (components.symm _) i = scalarEmbed (f i)
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem schwartzVector_ae (f : Fin 3 → 𝓢(Space, ℂ)) (i : Fin 3) :
    (fun x => schwartzVector f x i) =ᵐ[volume] fun x => f i (coordinateMap.symm x) := by
  have hc := coordinate_ae i (schwartzVector f)
  rw [coordinate_schwartzVector] at hc
  exact hc.symm.trans (scalarEmbed_ae (f i))

theorem fourier_ae_integral (f : Fin 3 → 𝓢(Space, ℂ)) (i : Fin 3) :
    (fun ξ => fourier (schwartzVector f) ξ i) =ᵐ[volume]
      fun ξ => 𝓕 (f i) (coordinateMap.symm ξ) := by
  have hc := coordinate_ae i (fourier (schwartzVector f))
  rw [fourier_coordinate, coordinate_schwartzVector] at hc
  exact hc.symm.trans (scalarFourier_ae_integral (f i))

def physicalProjection : VectorL2 →L[ℂ] VectorL2 :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    LongitudinalProjection.multiplier ∘L fourier.toContinuousLinearEquiv.toContinuousLinearMap

theorem physicalProjection_intertwine (f : VectorL2) :
    fourier (physicalProjection f) = LongitudinalProjection.multiplier (fourier f) := by
  exact fourier.apply_symm_apply _

theorem physicalProjection_norm (f : VectorL2) : ‖physicalProjection f‖ ≤ ‖f‖ := by
  rw [← fourier.norm_map (physicalProjection f), physicalProjection_intertwine]
  calc
    ‖LongitudinalProjection.multiplier (fourier f)‖ ≤ ‖fourier f‖ :=
      LongitudinalProjection.applyMultiplier_norm_le _
    _ = ‖f‖ := fourier.norm_map f

theorem physicalProjection_norm_le : ‖physicalProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa using physicalProjection_norm f

theorem physicalProjection_idempotent_apply (f : VectorL2) :
    physicalProjection (physicalProjection f) = physicalProjection f := by
  apply fourier.injective
  rw [physicalProjection_intertwine, physicalProjection_intertwine,
    LongitudinalProjection.multiplier_idempotent_apply]

theorem physicalProjection_idempotent : physicalProjection * physicalProjection = physicalProjection := by
  apply ContinuousLinearMap.ext
  exact physicalProjection_idempotent_apply

theorem physicalProjection_symmetric (f g : VectorL2) :
    ⟪physicalProjection f, g⟫_ℂ = ⟪f, physicalProjection g⟫_ℂ := by
  rw [← fourier.inner_map_map (physicalProjection f) g,
    ← fourier.inner_map_map f (physicalProjection g),
    physicalProjection_intertwine, physicalProjection_intertwine]
  exact LongitudinalProjection.multiplier_symmetric _ _

theorem physicalProjection_selfAdjoint : IsSelfAdjoint physicalProjection :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr physicalProjection_symmetric

theorem physicalProjection_positive : physicalProjection.IsPositive := by
  refine ⟨physicalProjection_selfAdjoint, ?_⟩
  intro f
  change 0 ≤ (⟪physicalProjection f, f⟫_ℂ).re
  have hi := physicalProjection_symmetric (physicalProjection f) f
  rw [physicalProjection_idempotent_apply] at hi
  rw [hi]
  simpa only [RCLike.re_eq_complex_re] using
    (inner_self_nonneg (𝕜 := ℂ) (x := physicalProjection f))

theorem physicalProjection_symbol (f : VectorL2) :
    fourier (physicalProjection f) =ᵐ[volume]
      fun ξ => LongitudinalProjection.symbol ξ (fourier f ξ) := by
  rw [physicalProjection_intertwine]
  exact LongitudinalProjection.multiplier_ae _

theorem physicalProjection_symbol_coordinate (f : VectorL2) (i : Fin 3) :
    (fun ξ => fourier (physicalProjection f) ξ i) =ᵐ[volume]
      fun ξ => ((∑ j, (ξ j : ℂ) * fourier f ξ j) /
        (∑ j, (ξ j : ℂ) ^ 2)) * (ξ i : ℂ) := by
  filter_upwards [physicalProjection_symbol f] with ξ hξ
  rw [hξ]
  exact LongitudinalProjection.symbol_coordinate ξ (fourier f ξ) i

end OQ14.VectorFourier

#print axioms OQ14.VectorFourier.coordinateMap_preserving
#print axioms OQ14.VectorFourier.scalarToFrom
#print axioms OQ14.VectorFourier.scalarFromTo
#print axioms OQ14.VectorFourier.scalarCoordinates_symm
#print axioms OQ14.VectorFourier.scalarEmbed_ae
#print axioms OQ14.VectorFourier.scalarFourier_embed
#print axioms OQ14.VectorFourier.scalarFourier_ae_integral
#print axioms OQ14.VectorFourier.coordinate_ae
#print axioms OQ14.VectorFourier.components_apply
#print axioms OQ14.VectorFourier.components_inner
#print axioms OQ14.VectorFourier.components_norm
#print axioms OQ14.VectorFourier.coordinate_insertion
#print axioms OQ14.VectorFourier.coordinate_assemble
#print axioms OQ14.VectorFourier.components_surjective
#print axioms OQ14.VectorFourier.components_coordinate
#print axioms OQ14.VectorFourier.fourier_norm
#print axioms OQ14.VectorFourier.fourier_inner
#print axioms OQ14.VectorFourier.fourier_coordinate
#print axioms OQ14.VectorFourier.coordinate_schwartzVector
#print axioms OQ14.VectorFourier.schwartzVector_ae
#print axioms OQ14.VectorFourier.fourier_ae_integral
#print axioms OQ14.VectorFourier.physicalProjection_intertwine
#print axioms OQ14.VectorFourier.physicalProjection_norm
#print axioms OQ14.VectorFourier.physicalProjection_norm_le
#print axioms OQ14.VectorFourier.physicalProjection_idempotent_apply
#print axioms OQ14.VectorFourier.physicalProjection_idempotent
#print axioms OQ14.VectorFourier.physicalProjection_symmetric
#print axioms OQ14.VectorFourier.physicalProjection_selfAdjoint
#print axioms OQ14.VectorFourier.physicalProjection_positive
#print axioms OQ14.VectorFourier.physicalProjection_symbol
#print axioms OQ14.VectorFourier.physicalProjection_symbol_coordinate
