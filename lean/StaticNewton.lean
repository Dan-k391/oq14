import NewtonL1L2
import StaticCoefficient

/-!
# The actual Newton volume response for bounded dielectric coefficients

The static response of a compactly supported bounded measurable material
source is identified through literal spatial Newton integrals. Its weighted
volume block is then the previously proved coercive block, with inverse
bound one. No dynamic response or weak Maxwell solution is assumed here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.StaticNewton

open MeasureTheory
open scoped SchwartzMap InnerProductSpace

abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

theorem material_source_ae (c : Coefficient) (u : VectorL2) (i : Fin 3) :
    NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) i =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        u (VectorFourier.coordinateMap x) i := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c u)
  filter_upwards [NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c u) i, h]
    with x hx hy
  rw [hx, hy]
  rfl

theorem material_source_integrable (c : Coefficient) (u : VectorL2)
    (K : Set Space) (hK : IsCompact K)
    (hc : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x) = 0) (i : Fin 3) :
    Integrable (NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) i :
      Space → ℂ) := by
  apply NewtonL1L2.compact_supported_integrable _ K hK
  filter_upwards [material_source_ae c u i] with x hx
  intro h
  rw [hx, hc x h]
  simp

def response (c : Coefficient) : VectorL2 →L[ℂ] VectorL2 :=
  NewtonL2.newtonOperator ∘L StaticCoefficient.sqrtMultiplier c

theorem response_norm (c : Coefficient) (u : VectorL2) :
    ‖response c u‖ ≤ Real.sqrt c.bound * ‖u‖ := by
  change ‖-VectorFourier.physicalProjection (StaticCoefficient.sqrtMultiplier c u)‖ ≤ _
  rw [norm_neg]
  exact (VectorFourier.physicalProjection_norm _).trans (StaticCoefficient.applySqrt_norm c u)

/-- The material response is the actual distributional Hessian of N convolved
with sqrt(chi) times the unknown field; every source integral is genuine. -/
theorem response_actual_spatial_pairing (c : Coefficient) (u : VectorL2)
    (K : Set Space) (hK : IsCompact K)
    (hc : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x) = 0)
    (g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x, response c u (VectorFourier.coordinateMap x) i * g x) =
      ∑ j, ∫ y, ((Real.sqrt (c.value (VectorFourier.coordinateMap y)) : ℂ) *
        u (VectorFourier.coordinateMap y) j) *
        ∫ x, GreenKernel.phi 0 (x - y) *
          (GradientProjection.pderivative i (GradientProjection.pderivative j g)) x := by
  have h := NewtonL1L2.newtonOperator_spatial_pairing
    (StaticCoefficient.sqrtMultiplier c u) (material_source_integrable c u K hK hc) g i
  simp_rw [NewtonConvolution.weakConvolution_spatial] at h
  calc
    _ = ∫ x, NewtonL2.physicalCoordinate
        (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u)) i x * g x := by
      apply integral_congr_ae
      filter_upwards [NewtonL2.physicalCoordinate_ae
        (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c u)) i] with x hx
      rw [hx]
      rfl
    _ = _ := h.trans (by
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [material_source_ae c u j] with y hy
      rw [hy])

def volumeBlock (c : Coefficient) : VectorL2 →L[ℂ] VectorL2 :=
  1 - StaticCoefficient.sqrtMultiplier c ∘L response c

theorem volumeBlock_eq (c : Coefficient) :
    volumeBlock c = StaticCoefficient.weightedBlock c := by
  apply ContinuousLinearMap.ext
  intro u
  change u - StaticCoefficient.sqrtMultiplier c
      (-VectorFourier.physicalProjection (StaticCoefficient.sqrtMultiplier c u)) =
    u + StaticCoefficient.sqrtMultiplier c
      (VectorFourier.physicalProjection (StaticCoefficient.sqrtMultiplier c u))
  rw [map_neg, sub_neg_eq_add]

theorem volumeBlock_ae (c : Coefficient) (u : VectorL2) :
    volumeBlock c u =ᵐ[volume] fun x => u x -
      (Real.sqrt (c.value x) : ℂ) • response c u x := by
  change u - StaticCoefficient.sqrtMultiplier c (response c u) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub u (StaticCoefficient.sqrtMultiplier c (response c u)),
    StaticCoefficient.sqrtMultiplier_ae c (response c u)] with x hx hy
  rw [hx]
  simp only [Pi.sub_apply, hy]

theorem volumeBlock_coercive (c : Coefficient) (u : VectorL2) :
    ‖u‖ ^ 2 ≤ (⟪volumeBlock c u, u⟫_ℂ).re := by
  rw [volumeBlock_eq]
  exact StaticCoefficient.weightedBlock_coercive c u

theorem volumeBlock_isUnit (c : Coefficient) : IsUnit (volumeBlock c) := by
  rw [volumeBlock_eq]
  exact StaticCoefficient.weightedBlock_isUnit c

theorem volumeBlock_inverse_norm_le (c : Coefficient) :
    ‖Ring.inverse (volumeBlock c)‖ ≤ 1 := by
  rw [volumeBlock_eq]
  exact StaticCoefficient.weightedBlock_inverse_norm_le c

end OQ14.StaticNewton

#print axioms OQ14.StaticNewton.material_source_ae
#print axioms OQ14.StaticNewton.material_source_integrable
#print axioms OQ14.StaticNewton.response_norm
#print axioms OQ14.StaticNewton.response_actual_spatial_pairing
#print axioms OQ14.StaticNewton.volumeBlock_eq
#print axioms OQ14.StaticNewton.volumeBlock_ae
#print axioms OQ14.StaticNewton.volumeBlock_coercive
#print axioms OQ14.StaticNewton.volumeBlock_isUnit
#print axioms OQ14.StaticNewton.volumeBlock_inverse_norm_le
