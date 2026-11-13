import Packet05GraphH1Pullback
import Packet05GraphConstitutive

/-! Almost-everywhere values of the constructed L² graph gradient agree with
the explicit covariant gradient used by the constitutive identity. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GraphGradientValues
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl
  OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphSmooth
  OQ14.Packet05GraphConstitutive
open OQ14.Maxwell (basis)
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem normal_slope_zero (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (x : Space) :
    slopeC g 2 x = 0 := by
  change ((fderiv ℝ (OQ14.Packet05PhysicalGraphChart.liftedHeight g) x (basis 2) : ℝ) : ℂ) = 0
  rw [liftedHeight_normal_derivative g (hg.of_le (by norm_num)) x]
  rfl

theorem pulledGradient_ae (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (U : L2Vector)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) (i : Fin 3) :
    (fun x => pulledGradient g hg U B hB i x) =ᵐ[volume]
      fun x => pullback g hg.continuous (U i) x + slopeC g i x * pullback g hg.continuous (U 2) x := by
  filter_upwards [Lp.coeFn_add (pullback g hg.continuous (U i))
    (slopeMul g hg i (B i) (hB i) (pullback g hg.continuous (U 2))),
    slopeMul_ae g hg i (B i) (hB i) (pullback g hg.continuous (U 2))] with x ha hs
  change (pullback g hg.continuous (U i) + slopeMul g hg i (B i) (hB i)
    (pullback g hg.continuous (U 2)) : L2Scalar) x = _
  rw [ha]
  simp only [Pi.add_apply, hs]

theorem pulledGradient_matches_chart (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (U : L2Vector)
    (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i) (i : Fin 3) :
    (fun x => pulledGradient g hg U B hB i x) =ᵐ[volume]
      fun x => Packet05GraphConstitutive.pulledGradient
        (OQ14.Packet05GraphSlope.slope g 0 x) (OQ14.Packet05GraphSlope.slope g 1 x)
        (fun j => pullback g hg.continuous (U j) x) i := by
  filter_upwards [pulledGradient_ae g hg U B hB i] with x hx
  rw [hx]
  have hz : OQ14.Packet05GraphSlope.slope g 2 x = 0 := liftedHeight_normal_derivative g (hg.of_le (by norm_num)) x
  fin_cases i <;> simp [Packet05GraphConstitutive.pulledGradient, slopeC, hz]

end OQ14.Packet05GraphGradientValues
#print axioms OQ14.Packet05GraphGradientValues.normal_slope_zero
#print axioms OQ14.Packet05GraphGradientValues.pulledGradient_ae
#print axioms OQ14.Packet05GraphGradientValues.pulledGradient_matches_chart
