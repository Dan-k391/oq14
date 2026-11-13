import Packet05RegionalDivergenceCongruence
import Packet05DifferentiatedScalarEquation

/-! Tangentially differentiate a scalar transmission equation only on an
interior region; the outer divergence source need only vanish there. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RegionalDifferentiatedScalar
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarEnergyIdentity
  OQ14.Packet05WeightedMatrixDerivative OQ14.Packet05DifferentiatedScalarEquation
  OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence OQ14.Packet05RegionalDivergenceCongruence

theorem regional_differentiated_scalar_equation (V : Set Space) (hV : IsOpen V)
    (A : Fin 3 → Fin 3 → Test) (hA : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (C C' DC F F' DF : L2Vector) (D : L2Scalar) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin 3) (hi : i ≠ 2)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j - F j) D)
    (hD : ∀ᵐ x ∂volume, x ∈ V → D x = 0)
    (hCeq : ∀ j, ∀ᵐ x ∂volume, x ∈ V → C' j x = C j x)
    (hFeq : ∀ j, ∀ᵐ x ∂volume, x ∈ V → F' j x = F j x)
    (hC' : ∀ j, HasWeakPartial (C' j) (DC j) i)
    (hF' : ∀ j, HasWeakPartial (F' j) (DF j) i) :
    HasDivergenceOn V
      (fun j => flux A DC d hd j - differentiatedSource A hA C' DF d hd i j) 0 := by
  have hdiv' : HasDivergenceOn V (fun j => flux A C' d hd j - F' j) D := by
    apply divergence_on_of_ae_eq V (fun j => flux A C d hd j - F j) _ D hdiv
    intro j
    filter_upwards [flux_local_ae_eq V A C C' d hd hCeq j, hFeq j,
      Lp.coeFn_sub (flux A C' d hd j) (F' j), Lp.coeFn_sub (flux A C d hd j) (F j)] with x hflux hf hs1 hs2 hx
    change (flux A C' d hd j - F' j : L2Scalar) x = (flux A C d hd j - F j : L2Scalar) x
    rw [hs1,hs2]
    simp only [Pi.sub_apply, hflux hx, hf hx]
  have hDlocal : HasPartialOn V D 0 i := by
    apply partial_on_of_ae_eq V D 0 0 i (global_partial_on V 0 0 i (by intro φ; simp))
    filter_upwards [hD, Lp.coeFn_zero ℂ (2 : ENNReal) (volume : Measure Space)] with x hx hz hVx
    rw [hx hVx,hz]
    rfl
  have hP (j : Fin 3) : HasWeakPartial (flux A C' d hd j - F' j)
      (flux A DC d hd j - differentiatedSource A hA C' DF d hd i j) i := by
    have hw := weighted_matrix_tangential_partial A hA C' DC d hd i j hi hC'
    have hf := hF' j
    intro φ
    have hw := hw φ
    have hf := hf φ
    rw [mulWeight_add] at hw
    simp only [map_add] at hw
    simp only [flux, differentiatedSource, map_sub]
    linear_combination hw - hf
  exact regional_partial_commutes_divergence V hV _ _ D 0 i hdiv'
    (fun j => global_partial_on V _ _ i (hP j)) hDlocal

end OQ14.Packet05RegionalDifferentiatedScalar
#print axioms OQ14.Packet05RegionalDifferentiatedScalar.regional_differentiated_scalar_equation
