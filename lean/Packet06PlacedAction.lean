import Packet06PhysicalPlacement
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PlacedAction
open MeasureTheory Metric OQ14.Maxwell OQ14.Packet06CyclicRotation
open OQ14.WeakCurl (previous)

theorem dilate_spatial_ae (s : ℝ) (hs : 0 < s) (u : VectorFourier.VectorL2) (i : Fin 3) :
    (fun x : Maxwell.Space => DilationL2.dilate s u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (s : ℂ)*u (VectorFourier.coordinateMap (s • x)) i := by
  have h := DilationL2.physicalCoordinate_dilate s hs u i
  have hc := NewtonL2.physicalCoordinate_ae (DilationL2.dilate s u) i
  have hu := DilationL2.ae_smul_space s hs.ne' (NewtonL2.physicalCoordinate_ae u i)
  filter_upwards [h,hc,hu] with x h hc hu
  rw [←hc,h,hu]

theorem placed_unknown_ae (s : ℝ) (hs : 0 < s) (a : Maxwell.Space)
    (u : VectorFourier.VectorL2) (i : Fin 3) :
    (fun y : Maxwell.Space => Packet06PlacedKernel.placedUnknown s a u (VectorFourier.coordinateMap y) i) =ᵐ[volume]
      fun y => ((Real.sqrt s*s : ℝ) : ℂ)*u (VectorFourier.coordinateMap (unrotate (s • (y-a)))) (previous i) := by
  let ur := Packet06CyclicL2.action u
  let ud := DilationL2.dilate s ur
  have ht := Packet06TranslationL2.action_ae a ((Real.sqrt s : ℂ) • ud) i
  have hsm := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_smul (Real.sqrt s : ℂ) ud)
  have hd := dilate_spatial_ae s hs ur i
  have hr := DilationL2.ae_smul_space s hs.ne' (Packet06CyclicL2.action_ae u i)
  have hshift := (measurePreserving_add_right (volume : Measure Maxwell.Space) (-a)).quasiMeasurePreserving.ae
    (hsm.and (hd.and hr))
  filter_upwards [ht,hshift] with y ht hy
  change Packet06TranslationL2.action a ((Real.sqrt s : ℂ) • ud) (VectorFourier.coordinateMap y) i = _ at ht
  change Packet06TranslationL2.action a ((Real.sqrt s : ℂ) • ud) (VectorFourier.coordinateMap y) i = _
  rw [ht]
  have hsm' := congrArg (fun v : VectorFourier.Vector => v i) hy.1
  simp only [sub_eq_add_neg,PiLp.smul_apply,smul_eq_mul] at hsm' ⊢
  rw [hsm']
  change (Real.sqrt s : ℂ)*DilationL2.dilate s ur (VectorFourier.coordinateMap (y + -a)) i = _
  rw [hy.2.1,hy.2.2]
  push_cast
  ring
#print axioms OQ14.Packet06PlacedAction.dilate_spatial_ae
#print axioms OQ14.Packet06PlacedAction.placed_unknown_ae
end OQ14.Packet06PlacedAction
