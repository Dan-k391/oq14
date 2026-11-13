import Packet06SectorFamily
import Packet06SymmetryPencil

/-! Actual invariant electric-sector pencils for general symmetric materials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06MaterialSector
open Filter Set Metric MeasureTheory Packet06SectorOperator Packet06SectorFamily
open StaticCoefficient (Coefficient)
open scoped Topology

def pencil (c : Coefficient) (R : ℝ) (z : ℂ) : Sector →L[ℂ] Sector :=
  compression (ComplexConvolutionAnalytic.pencil c z R)

theorem pencil_actual (c : Coefficient) (ha : Packet06MaterialSymmetry.Axial c)
    (hm : Packet06MaterialSymmetry.Meridional c) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x : FourierL2.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : Sector) :
    ((pencil c R z u : Sector) : VectorL2) = ComplexConvolutionAnalytic.pencil c z R u :=
  compression_actual _ (Packet06SymmetryPencil.pencil_mem_electricSector c ha hm R hR hsupp z) u

theorem pencil_analyticAt (c : Coefficient) (R : ℝ) (hR : 0 ≤ R) (z : ℂ) :
    AnalyticAt ℂ (pencil c R) z :=
  compression_analyticAt _ z (ComplexConvolutionAnalytic.pencil_analyticAt c z R hR)

theorem pencil_locally_uniform (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : FourierL2.Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : FourierL2.Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0) :
    TendstoLocallyUniformlyOn (fun n z => pencil (c n) R z) (pencil c₀ R) atTop univ :=
  compression_locally_uniform _ _ univ isOpen_univ
    (Packet06WeightedPencilHolomorphic.pencil_locally_uniform c c₀ D R hR hb hb₀ ha hc hc₀)

theorem pencil_kernel_actual (c : Coefficient) (ha : Packet06MaterialSymmetry.Axial c)
    (hm : Packet06MaterialSymmetry.Meridional c) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x : FourierL2.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : Sector) :
    pencil c R z u = 0 ↔ ComplexConvolutionAnalytic.volumeBlock c z R u = 0 := by
  have hp := compression_kernel_actual _
    (Packet06SymmetryPencil.pencil_mem_electricSector c ha hm R hR hsupp z) u
  change pencil c R z u = 0 ↔ ComplexConvolutionAnalytic.pencil c z R u = 0 at hp
  rw [hp,ComplexConvolutionAnalytic.volumeBlock_factor]
  constructor
  · intro h
    change StaticNewton.volumeBlock c (ComplexConvolutionAnalytic.pencil c z R u) = 0
    rw [h,map_zero]
  · intro h
    have hh := congrArg (fun v : VectorL2 => Ring.inverse (StaticNewton.volumeBlock c) v) h
    dsimp only at hh
    change (Ring.inverse (StaticNewton.volumeBlock c)*StaticNewton.volumeBlock c*
      ComplexConvolutionAnalytic.pencil c z R) u = _ at hh
    rw [Ring.inverse_mul_cancel _ (StaticNewton.volumeBlock_isUnit c),one_mul,map_zero] at hh
    exact hh

theorem sphere_pencil (n : ℝ) (hn : 1 < n) :
    pencil (ModalWeightedMode.coefficient n hn) 1 = Packet06SphereReduced.pencil n hn :=
  funext (Packet06SectorFamily.sphere_pencil n hn)

end OQ14.Packet06MaterialSector
#print axioms OQ14.Packet06MaterialSector.pencil_actual
#print axioms OQ14.Packet06MaterialSector.pencil_analyticAt
#print axioms OQ14.Packet06MaterialSector.pencil_locally_uniform
#print axioms OQ14.Packet06MaterialSector.pencil_kernel_actual
#print axioms OQ14.Packet06MaterialSector.sphere_pencil
