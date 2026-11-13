import Packet06PlacedSector
import Packet06ProjectedPhysicalResidue
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06PlacedProjection
open MeasureTheory Maxwell Packet06PlacedEquivalence Packet06SectorOperator
open scoped InnerProductSpace
abbrev V := VectorFourier.VectorL2

theorem cyclic_inner (u v : V) :
    ⟪Packet06CyclicL2.action u, Packet06CyclicL2.action v⟫_ℂ = ⟪u,v⟫_ℂ := by
  rw [← VectorFourier.components_inner, ← VectorFourier.components_inner u v]
  simp only [PiLp.inner_apply,VectorFourier.components_apply]
  have hc (i : Fin 3) : ⟪VectorFourier.coordinate i (Packet06CyclicL2.action u),
      VectorFourier.coordinate i (Packet06CyclicL2.action v)⟫_ℂ =
      ⟪VectorFourier.coordinate (WeakCurl.previous i) u,VectorFourier.coordinate (WeakCurl.previous i) v⟫_ℂ := by
    rw [← VectorFourier.scalarCoordinates.inner_map_map, ← VectorFourier.scalarCoordinates.inner_map_map]
    change ⟪DynamicConvolution.component i (Packet06CyclicL2.action u),
      DynamicConvolution.component i (Packet06CyclicL2.action v)⟫_ℂ = _
    rw [Packet06CyclicL2.component_action,Packet06CyclicL2.component_action]
    exact (Lp.compMeasurePreservingₗᵢ ℂ
      (Packet06CyclicRotation.rotation.symm : Space → Space)
      Packet06CyclicRotation.rotation.symm.measurePreserving).inner_map_map
        (DynamicConvolution.component (WeakCurl.previous i) u)
        (DynamicConvolution.component (WeakCurl.previous i) v)
  simp [Fin.sum_univ_three,hc,WeakCurl.previous]
  ring

theorem translation_inner (a : Space) (u v : V) :
    ⟪Packet06TranslationL2.action a u, Packet06TranslationL2.action a v⟫_ℂ = ⟪u,v⟫_ℂ := by
  rw [← VectorFourier.components_inner, ← VectorFourier.components_inner u v]
  simp only [PiLp.inner_apply,VectorFourier.components_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← VectorFourier.scalarCoordinates.inner_map_map, ← VectorFourier.scalarCoordinates.inner_map_map]
  change ⟪DynamicConvolution.component i (Packet06TranslationL2.action a u),
    DynamicConvolution.component i (Packet06TranslationL2.action a v)⟫_ℂ = _
  rw [Packet06TranslationL2.component_action,Packet06TranslationL2.component_action]
  exact (StaticBallTranslation.scalar a).inner_map_map _ _

theorem placed_inner (s : ℝ) (hs : 0 < s) (a : Space) (u v : V) :
    ⟪placed s hs a u, placed s hs a v⟫_ℂ = ⟪u,v⟫_ℂ := by
  rw [placed_apply,placed_apply]
  dsimp only [Packet06PlacedKernel.placedUnknown]
  rw [translation_inner,inner_smul_left,inner_smul_right,Complex.conj_ofReal,
    DilationL2.dilate_inner s hs,cyclic_inner]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hsqrt : (Real.sqrt s : ℂ)*(Real.sqrt s : ℂ) = (s : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hs.le
  rw [← mul_assoc, ← mul_assoc, hsqrt, Complex.ofReal_inv, mul_inv_cancel₀ hs0, one_mul]

theorem placed_norm (s : ℝ) (hs : 0 < s) (a : Space) (u : V) : ‖placed s hs a u‖ = ‖u‖ := by
  have h := congrArg Complex.re (placed_inner s hs a u u)
  have h1 : (⟪placed s hs a u, placed s hs a u⟫_ℂ).re = ‖placed s hs a u‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) (placed s hs a u))
  have h2 : (⟪u,u⟫_ℂ).re = ‖u‖^2 := by
    simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) u)
  rw [h1,h2] at h
  nlinarith [norm_nonneg (placed s hs a u), norm_nonneg u]

def placedIso (s : ℝ) (hs : 0 < s) (a : Space) : V ≃ₗᵢ[ℂ] V :=
  { (placed s hs a).toLinearEquiv with norm_map' := placed_norm s hs a }

def placedSector (s : ℝ) (hs : 0 < s) (a : Space) : Submodule ℂ V :=
  Sector.map (placedIso s hs a).toLinearMap

instance placedSector_complete (s : ℝ) (hs : 0 < s) (a : Space) :
    CompleteSpace (placedSector s hs a) := by
  have hc : IsClosed (placedSector s hs a : Set V) := by
    change IsClosed ((placedIso s hs a) '' (Sector : Set V))
    exact (placedIso s hs a).toHomeomorph.isClosedMap _ ModalMeridionalReflection.electricSector_closed
  exact hc.completeSpace_coe

theorem projected_transport (s : ℝ) (hs : 0 < s) (a : Space) (f : V) :
    ((placedSector s hs a).orthogonalProjection f : V) =
      placedIso s hs a (Sector.orthogonalProjection ((placedIso s hs a).symm f)) := by
  exact Submodule.orthogonalProjection_map_apply (placedIso s hs a) Sector f

#print axioms OQ14.Packet06PlacedProjection.cyclic_inner
#print axioms OQ14.Packet06PlacedProjection.translation_inner
#print axioms OQ14.Packet06PlacedProjection.placed_inner
#print axioms OQ14.Packet06PlacedProjection.placed_norm
#print axioms OQ14.Packet06PlacedProjection.projected_transport
end OQ14.Packet06PlacedProjection
