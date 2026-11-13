import Packet06MagneticOutgoing

/-! The global physical electric mode retains the exact weighted volume
unknown; a nonzero kernel therefore yields a nonzero physical field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PhysicalMode
open MeasureTheory Metric Filter DynamicSource Packet06GlobalField
open StaticCoefficient (Coefficient)
open scoped Topology

theorem weighted_electric_ae (c : Coefficient) (z : ℂ) (S : ℝ) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (i : Fin 3) :
    (fun x : Maxwell.Space => u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*electric c z S u x i := by
  have hw : StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.response c z S (S+1) u) = u := by
    simpa only [sub_zero] using Packet06GreenSource.solved_weighted_response c z S (S+1) (by linarith) u 0 hc hu
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c (Packet06LocalPencil.response c z S (S+1) u))
  rw [hw] at hs
  filter_upwards [hs] with x hx
  have hi := congrArg (fun v : VectorFourier.Vector => v i) hx
  change u (VectorFourier.coordinateMap x) i =
    (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*
      Packet06LocalPencil.response c z S (S+1) u (VectorFourier.coordinateMap x) i at hi
  rw [hi]
  by_cases hcore : ‖x‖ ≤ S+1
  · rw [electric,if_pos hcore]
    rfl
  · have hz : c.value (VectorFourier.coordinateMap x) = 0 := hc x (by
      simp only [mem_closedBall,dist_zero_right]
      linarith)
    simp [hz]

theorem electric_nonzero (c : Coefficient) (z : ℂ) (S : ℝ) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hne : u ≠ 0) :
    ¬ ∀ i : Fin 3, (fun x : Maxwell.Space => electric c z S u x i) =ᵐ[volume] 0 := by
  intro hzero
  apply hne
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hz := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_zero VectorFourier.Vector 2 (volume : Measure StaticCoefficient.Space))
  filter_upwards [weighted_electric_ae c z S u hc hu i,hzero i,hz] with x hx he hz
  rw [hx,he]
  have hzi := congrArg (fun v : VectorFourier.Vector => v i) hz
  change (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*(0 : ℂ) = _
  rw [mul_zero]
  exact hzi.symm

end OQ14.Packet06PhysicalMode
#print axioms OQ14.Packet06PhysicalMode.weighted_electric_ae
#print axioms OQ14.Packet06PhysicalMode.electric_nonzero
