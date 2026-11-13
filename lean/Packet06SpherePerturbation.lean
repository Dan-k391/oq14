import Packet06ActualModePersistence
import Packet06SphereReducedSchur
import Packet06SphereSymmetry

/-! Actual symmetric material perturbations of the proved simple sphere mode.
All kernel, field and physical normalization conclusions use the same branch. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SpherePerturbation
open Filter Set Metric MeasureTheory Packet06SectorOperator
open StaticCoefficient (Coefficient)
open Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology

theorem actual_sphere_mode_persistence (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z₀ : ℂ) (hz₀ : z₀ ≠ 0)
    (hdet : ModalAlgebra.tmDet 1 (n : ℂ) z₀ = 0)
    (c : ℕ → Coefficient) (D : ℝ) (hb : ∀ j, (c j).bound ≤ D)
    (hb₀ : (ModalWeightedMode.coefficient n hn).bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun j => (c j).value x) atTop
      (𝓝 ((ModalWeightedMode.coefficient n hn).value x)))
    (hc : ∀ (j : ℕ) (x : FourierL2.Space), x ∉ closedBall 0 1 → (c j).value (VectorFourier.coordinateMap x) = 0)
    (hax : ∀ j, Packet06MaterialSymmetry.Axial (c j))
    (hmer : ∀ j, Packet06MaterialSymmetry.Meridional (c j)) :
    ∃ (ψ : Sector →L[ℂ] ℂ) (z : ℕ → ℂ) (u : ℕ → Sector),
      ψ (numerator n hn z₀) = 1 ∧
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto u atTop (𝓝 (numerator n hn z₀)) ∧
      (∀ T : ℝ, 1 ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (c j) (z j) 1 T (u j)) atTop
        (𝓝 (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z₀ 1 T (numerator n hn z₀)))) ∧
      Tendsto (fun j => reciprocalNorm (c j) 1 (z j) (u j)) atTop
        (𝓝 (reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z₀ (numerator n hn z₀))) ∧
      (∀ᶠ j in atTop, z j ≠ 0 ∧ u j ≠ 0 ∧
        ComplexConvolutionAnalytic.volumeBlock (c j) (z j) 1 (u j) = 0 ∧ ψ (u j) = 1 ∧
        (∀ v : Sector, ComplexConvolutionAnalytic.volumeBlock (c j) (z j) 1 v = 0 ↔ v = ψ v • u j) ∧
        reciprocalNorm (c j) 1 (z j) (u j) ≠ 0) := by
  obtain ⟨w,ψ,hψ,_,hunit,_,_,hder,hd,_⟩ :=
    Packet06SphereReducedSchur.actual_scalar_reduction n hn hna z₀ hz₀ hdet
  rw [←Packet06MaterialSector.sphere_pencil n hn] at hunit hder
  have hscalar : deriv (fun z => Packet06ScalarSchur.scalar
      (Packet06MaterialSector.pencil (ModalWeightedMode.coefficient n hn) 1 z) w ψ) z₀ ≠ 0 := by
    rw [hder.deriv]
    exact hd
  obtain ⟨z,u,hz,hu,hgood⟩ := Packet06ActualModePersistence.actual_kernel_modes
    c (ModalWeightedMode.coefficient n hn) D 1 (by norm_num) hb hb₀ ha hc
    (ModalWeightedMode.coefficient_support n hn) hax hmer
    (Packet06SphereSymmetry.sphere_axial n hn) (Packet06SphereSymmetry.sphere_meridional n hn)
    z₀ hz₀ (numerator n hn z₀) w ψ hunit
    (ModalSphereVolumeKernel.numerator_in_kernel n hn z₀ hz₀ hdet).2 hψ hscalar
  have huV : Tendsto (fun j => (u j : VectorL2)) atTop (𝓝 (numerator n hn z₀ : VectorL2)) :=
    Sector.subtypeL.continuous.tendsto _ |>.comp hu
  have hnorm := Packet06ResponseLimit.reciprocalNorm_tendsto c (ModalWeightedMode.coefficient n hn)
    D 1 (by norm_num) hb hb₀ ha z z₀ hz (fun j => (u j : VectorL2)) (numerator n hn z₀) huV
  have hN₀ : reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z₀ (numerator n hn z₀) ≠ 0 :=
    Packet06PhysicalNormalization.reciprocalNorm_nonzero _ 1 (by norm_num) z₀ hz₀ _
      (ModalVolumeNormalization.numerator_pairing_nonzero n hn z₀ hz₀ hdet
        (Packet06SpherePole.determinant_simple n hn hna z₀ hz₀ hdet))
  refine ⟨ψ,z,u,hψ,hz,hu,?_,hnorm,?_⟩
  · intro T hT
    exact Packet06ResponseLimit.response_tendsto c (ModalWeightedMode.coefficient n hn)
      D 1 T (by linarith) hb hb₀ ha z z₀ hz (fun j => (u j : VectorL2)) (numerator n hn z₀) huV
  · filter_upwards [hgood,hnorm.eventually_ne hN₀] with j hj hNj
    exact ⟨hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1,hNj⟩

end OQ14.Packet06SpherePerturbation
#print axioms OQ14.Packet06SpherePerturbation.actual_sphere_mode_persistence
