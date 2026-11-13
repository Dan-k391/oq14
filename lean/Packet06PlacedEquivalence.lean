import Packet06PlacedKernel

/-! The actual field-placement maps form a continuous linear equivalence on L2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PlacedEquivalence
open MeasureTheory Maxwell Packet06CyclicRotation
abbrev V := VectorFourier.VectorL2

theorem cyclic_cube (u : V) :
    Packet06CyclicL2.action (Packet06CyclicL2.action (Packet06CyclicL2.action u))=u := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have h1 := Packet06CyclicL2.action_ae (Packet06CyclicL2.action (Packet06CyclicL2.action u)) i
  have h2 := rotation.symm.measurePreserving.quasiMeasurePreserving.ae
    (Packet06CyclicL2.action_ae (Packet06CyclicL2.action u) (WeakCurl.previous i))
  have h3 := rotation.symm.measurePreserving.quasiMeasurePreserving.ae
    (rotation.symm.measurePreserving.quasiMeasurePreserving.ae
      (Packet06CyclicL2.action_ae u (WeakCurl.previous (WeakCurl.previous i))))
  filter_upwards [h1,h2,h3] with x h1 h2 h3
  change Packet06CyclicL2.action (Packet06CyclicL2.action u)
    (VectorFourier.coordinateMap (unrotate x)) (WeakCurl.previous i) =
    Packet06CyclicL2.action u (VectorFourier.coordinateMap (unrotate (unrotate x)))
      (WeakCurl.previous (WeakCurl.previous i)) at h2
  change Packet06CyclicL2.action u (VectorFourier.coordinateMap (unrotate (unrotate x)))
    (WeakCurl.previous (WeakCurl.previous i)) =
    u (VectorFourier.coordinateMap (unrotate (unrotate (unrotate x))))
      (WeakCurl.previous (WeakCurl.previous (WeakCurl.previous i))) at h3
  rw [h1,h2,h3]
  have hspace : unrotate (unrotate (unrotate x))=x := by
    ext k
    fin_cases k <;> simp [unrotate,WeakCurl.next]
  have hcoord : WeakCurl.previous (WeakCurl.previous (WeakCurl.previous i))=i := by
    fin_cases i <;> rfl
  rw [hspace,hcoord]

theorem translation_inverse (a : Space) (u : V) :
    Packet06TranslationL2.action (-a) (Packet06TranslationL2.action a u)=u := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have h := (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
    (Packet06TranslationL2.action_ae a u i)
  filter_upwards [Packet06TranslationL2.action_ae (-a) (Packet06TranslationL2.action a u) i,h] with x hx hh
  rw [hx]
  simpa only [sub_neg_eq_add,add_sub_cancel_right] using hh

def ofInverse (A B : V →L[ℂ] V) (hBA : ∀ u,B (A u)=u) (hAB : ∀ u,A (B u)=u) : V ≃L[ℂ] V where
  toFun := A
  invFun := B
  left_inv := hBA
  right_inv := hAB
  map_add' := map_add A
  map_smul' := map_smul A
  continuous_toFun := A.continuous
  continuous_invFun := B.continuous

def cyclic : V ≃L[ℂ] V := ofInverse Packet06CyclicL2.action
  (Packet06CyclicL2.action.comp Packet06CyclicL2.action) cyclic_cube cyclic_cube

def translation (a : Space) : V ≃L[ℂ] V := ofInverse (Packet06TranslationL2.action a)
  (Packet06TranslationL2.action (-a)) (translation_inverse a)
  (by intro u; simpa only [neg_neg] using translation_inverse (-a) u)

def dilation (s : ℝ) (hs : 0 < s) : V ≃L[ℂ] V := ofInverse (DilationL2.dilate s)
  (DilationL2.dilate s⁻¹)
  (fun u => congrArg (fun A : V →L[ℂ] V => A u) (DilationL2.dilate_inv_comp s hs))
  (fun u => congrArg (fun A : V →L[ℂ] V => A u) (DilationL2.dilate_comp_inv s hs))

def amplitude (a : ℂ) (ha : a ≠ 0) : V ≃L[ℂ] V where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℂ V a ha
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

def placed (s : ℝ) (hs : 0 < s) (a : Space) : V ≃L[ℂ] V :=
  ((cyclic.trans (dilation s hs)).trans
    (amplitude (Real.sqrt s : ℂ) (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hs)))).trans
    (translation a)

theorem placed_apply (s : ℝ) (hs : 0 < s) (a : Space) (u : V) :
    placed s hs a u=Packet06PlacedKernel.placedUnknown s a u := rfl

theorem placed_injective (s : ℝ) (hs : 0 < s) (a : Space) :
    Function.Injective (Packet06PlacedKernel.placedUnknown s a) := (placed s hs a).injective

theorem placed_surjective (s : ℝ) (hs : 0 < s) (a : Space) :
    Function.Surjective (Packet06PlacedKernel.placedUnknown s a) := (placed s hs a).surjective

end OQ14.Packet06PlacedEquivalence
#print axioms OQ14.Packet06PlacedEquivalence.cyclic_cube
#print axioms OQ14.Packet06PlacedEquivalence.translation_inverse
#print axioms OQ14.Packet06PlacedEquivalence.placed_apply
#print axioms OQ14.Packet06PlacedEquivalence.placed_injective
#print axioms OQ14.Packet06PlacedEquivalence.placed_surjective
