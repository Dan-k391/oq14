import Packet05GraphSlopeNormal
import WeakPoynting.Green

/-! Bounded graph slopes act on actual L² fields. Their normal derivative
vanishes in compact test products. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphSlopeMultiplier
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.Packet05GraphSlope OQ14.Packet05GraphSlopeNormal
open OQ14.Maxwell (basis dcoord)
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def slopeC (g : Plane → ℝ) (i : Fin 3) (x : Space) : ℂ := (OQ14.Packet05GraphSlope.slope g i x : ℂ)

theorem slopeC_contDiff (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3) :
    ContDiff ℝ 1 (slopeC g i) := Complex.ofRealCLM.contDiff.comp (slope_contDiff g hg i)

theorem slopeC_normal_derivative (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3) (x : Space) :
    dcoord (slopeC g i) x 2 = 0 := by
  change fderiv ℝ (fun y => (OQ14.Packet05GraphSlope.slope g i y : ℂ)) x (basis 2) = 0
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x
    ((slope_contDiff g hg i).differentiable (by norm_num) x).hasFDerivAt
  change fderiv ℝ (Complex.ofRealCLM ∘ OQ14.Packet05GraphSlope.slope g i) x (basis 2) = 0
  rw [hd.fderiv]
  change Complex.ofRealCLM ((fderiv ℝ (OQ14.Packet05GraphSlope.slope g i) x) (basis 2)) = 0
  rw [slope_normal_derivative g hg i x, map_zero]

theorem slopeC_memLp_top (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    (B : ℝ) (hB : ∀ x, ‖slopeC g i x‖ ≤ B) : MemLp (slopeC g i) ⊤ volume := by
  exact memLp_top_of_bound (slopeC_contDiff g hg i).continuous.measurable.aestronglyMeasurable B
    (Filter.Eventually.of_forall hB)

def slopeMul (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    (B : ℝ) (hB : ∀ x, ‖slopeC g i x‖ ≤ B) (u : L2Scalar) : L2Scalar :=
  ((Lp.memLp u).mul' (slopeC_memLp_top g hg i B hB)).toLp (fun x => slopeC g i x * u x)

theorem slopeMul_ae (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3)
    (B : ℝ) (hB : ∀ x, ‖slopeC g i x‖ ≤ B) (u : L2Scalar) :
    (fun x => slopeMul g hg i B hB u x) =ᵐ[volume] fun x => slopeC g i x * u x :=
  ((Lp.memLp u).mul' (slopeC_memLp_top g hg i B hB)).coeFn_toLp

end OQ14.Packet05GraphSlopeMultiplier
#print axioms OQ14.Packet05GraphSlopeMultiplier.slopeC_contDiff
#print axioms OQ14.Packet05GraphSlopeMultiplier.slopeC_normal_derivative
#print axioms OQ14.Packet05GraphSlopeMultiplier.slopeC_memLp_top
#print axioms OQ14.Packet05GraphSlopeMultiplier.slopeMul_ae
