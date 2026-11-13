import Packet02SurfaceGeometry
import Packet02RadialLog
import Packet02GoodSet

/-! The inverse-square majorant on every fixed positive-radius sphere. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet02SurfaceL2
open MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.ModalWeightedMode

theorem angular_memLp (r : ℝ) (hr : 0 < r) :
    MemLp (Packet02Majorant.angular r) 2 volume :=
  (memLp_congr_ae (Packet02SurfaceGeometry.angular_formula_ae r hr)).mpr
    (Packet02RadialLog.profile_memLp r hr)

theorem source_memLp (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) (l : Fin 3) :
    MemLp (DynamicVolume.source (coefficient n hn) u l) 2 volume := by
  exact (Lp.memLp (NewtonL2.physicalCoordinate
    (StaticCoefficient.sqrtMultiplier (coefficient n hn) u) l)).ae_eq
      (StaticNewton.material_source_ae (coefficient n hn) u l)

theorem inverseSquare_joint (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (r : ℝ) (hr : 0 < r) (l : Fin 3) :
    Integrable (fun p : Sphere × Space => DynamicVolume.source (coefficient n hn) u l p.2 *
      Packet02GoodSet.inverseSquare (r • (p.1 : Space) - p.2)) (angularMeasure.prod volume) := by
  simpa only [Packet02Majorant.kernel, Packet02GoodSet.inverseSquare] using
    Packet02Majorant.joint_complex_integrable r (DynamicVolume.source (coefficient n hn) u l)
      (source_memLp n hn u l) (angular_memLp r hr)

end OQ14.Packet02SurfaceL2
#print axioms OQ14.Packet02SurfaceL2.angular_memLp
#print axioms OQ14.Packet02SurfaceL2.source_memLp
#print axioms OQ14.Packet02SurfaceL2.inverseSquare_joint
