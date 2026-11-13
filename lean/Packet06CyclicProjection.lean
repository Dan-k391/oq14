import Packet06CyclicFourier
import ModalAxialSymbol

/-! Cyclic rotation commutes with the actual longitudinal Fourier projection. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06CyclicProjection
open MeasureTheory Maxwell Packet06CyclicRotation Packet06CyclicL2 Packet06CyclicFourier
open WeakCurl (previous)

def rotateVector (v : VectorFourier.Vector) : VectorFourier.Vector :=
  (WithLp.equiv 2 (Fin 3 → ℂ)).symm (fun i => v (previous i))

theorem symbol_cov (x : Space) (v : VectorFourier.Vector) (i : Fin 3) :
    LongitudinalProjection.symbol (VectorFourier.coordinateMap (unrotate x)) v (previous i) =
      LongitudinalProjection.symbol (VectorFourier.coordinateMap x) (rotateVector v) i := by
  have hu (j : Fin 3) : VectorFourier.coordinateMap (unrotate x) j = x (WeakCurl.next j) := rfl
  have hx (j : Fin 3) : VectorFourier.coordinateMap x j = x j := rfl
  have hdot : (∑ j : Fin 3, (VectorFourier.coordinateMap (unrotate x) j : ℂ) * v j) =
      ∑ j : Fin 3, (VectorFourier.coordinateMap x j : ℂ) * rotateVector v j := by
    simp [hu,hx,rotateVector,WeakCurl.next,WeakCurl.previous,Fin.sum_univ_three]
    ring
  have hsquare : (∑ j : Fin 3, (VectorFourier.coordinateMap (unrotate x) j : ℂ)^2) =
      ∑ j : Fin 3, (VectorFourier.coordinateMap x j : ℂ)^2 := by
    simp [hu,hx,WeakCurl.next,Fin.sum_univ_three]
    ring
  rw [LongitudinalProjection.symbol_coordinate, LongitudinalProjection.symbol_coordinate, hdot, hsquare]
  congr 1
  fin_cases i <;> simp [hu,hx,WeakCurl.next,WeakCurl.previous]

theorem action_multiplier (F : VectorFourier.VectorL2) :
    action (LongitudinalProjection.multiplier F) = LongitudinalProjection.multiplier (action F) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hM := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (LongitudinalProjection.multiplier_ae F)
  have hM' := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (LongitudinalProjection.multiplier_ae (action F))
  have hU : ∀ᵐ x : Space ∂volume, ∀ j : Fin 3,
      action F (VectorFourier.coordinateMap x) j =
        F (VectorFourier.coordinateMap (unrotate x)) (previous j) := ae_all_iff.mpr (action_ae F)
  have hr := rotation.symm.measurePreserving.quasiMeasurePreserving.ae hM
  filter_upwards [action_ae (LongitudinalProjection.multiplier F) i, hr, hM', hU] with x h1 h2 h3 h4
  rw [h1, h3]
  have hv : action F (VectorFourier.coordinateMap x) =
      rotateVector (F (VectorFourier.coordinateMap (unrotate x))) := by
    ext j
    rw [h4 j]
    rfl
  rw [hv]
  change LongitudinalProjection.multiplier F (VectorFourier.coordinateMap (unrotate x)) (previous i) = _
  have h2' : LongitudinalProjection.multiplier F (VectorFourier.coordinateMap (unrotate x)) =
      LongitudinalProjection.symbol (VectorFourier.coordinateMap (unrotate x))
        (F (VectorFourier.coordinateMap (unrotate x))) := h2
  rw [h2']
  exact symbol_cov x _ i

theorem action_fourier_symm (F : VectorFourier.VectorL2) :
    action (VectorFourier.fourier.symm F) = VectorFourier.fourier.symm (action F) := by
  apply VectorFourier.fourier.injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← action_fourier,
    LinearIsometryEquiv.apply_symm_apply]

theorem action_projection (F : VectorFourier.VectorL2) :
    action (VectorFourier.physicalProjection F) = VectorFourier.physicalProjection (action F) := by
  unfold VectorFourier.physicalProjection
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [action_fourier_symm, action_multiplier, action_fourier]

/-- The actual static volume block intertwines with rotation of both the
    coefficient and the L² field. -/
theorem static_volume_conjugacy (c : StaticCoefficient.Coefficient) (F : VectorFourier.VectorL2) :
    StaticNewton.volumeBlock (Packet06CyclicMaterial.coefficient c) (action F) =
      action (StaticNewton.volumeBlock c F) := by
  rw [StaticNewton.volumeBlock_eq, StaticNewton.volumeBlock_eq]
  unfold StaticCoefficient.weightedBlock
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, map_add]
  rw [Packet06CyclicMaterial.multiplier_action, ← action_projection,
    ← Packet06CyclicMaterial.multiplier_action]
end OQ14.Packet06CyclicProjection
#print axioms OQ14.Packet06CyclicProjection.symbol_cov
#print axioms OQ14.Packet06CyclicProjection.action_multiplier
#print axioms OQ14.Packet06CyclicProjection.action_fourier_symm
#print axioms OQ14.Packet06CyclicProjection.action_projection
#print axioms OQ14.Packet06CyclicProjection.static_volume_conjugacy
