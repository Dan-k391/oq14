import Packet06MaterialSector
import Packet06SchurModeLimit
import Packet06ResponseLimit

/-! Persistence of actual symmetric-material Maxwell volume kernels, retaining
the same selected frequency and normalized mode sequences. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ActualModePersistence
open Filter Set Metric MeasureTheory Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
open StaticCoefficient (Coefficient)
open Packet06MaterialSector (pencil)
open scoped Topology

theorem actual_kernel_modes (c : ℕ → Coefficient) (c₀ : Coefficient) (D R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : FourierL2.Space), x ∉ closedBall 0 R → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : FourierL2.Space, x ∉ closedBall 0 R → c₀.value (VectorFourier.coordinateMap x) = 0)
    (hax : ∀ n, Packet06MaterialSymmetry.Axial (c n))
    (hmer : ∀ n, Packet06MaterialSymmetry.Meridional (c n))
    (hax₀ : Packet06MaterialSymmetry.Axial c₀) (hmer₀ : Packet06MaterialSymmetry.Meridional c₀)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (u₀ w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hunit : IsUnit (repair (pencil c₀ R z₀) w ψ))
    (hu₀ : ComplexConvolutionAnalytic.volumeBlock c₀ z₀ R u₀ = 0) (hψ : ψ u₀ = 1)
    (hd : deriv (fun z => scalar (pencil c₀ R z) w ψ) z₀ ≠ 0) :
    ∃ (z : ℕ → ℂ) (u : ℕ → Sector),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto u atTop (𝓝 u₀) ∧
      (∀ᶠ n in atTop, z n ≠ 0 ∧ u n ≠ 0 ∧
        ComplexConvolutionAnalytic.volumeBlock (c n) (z n) R (u n) = 0 ∧ ψ (u n) = 1 ∧
        (∀ v : Sector, ComplexConvolutionAnalytic.volumeBlock (c n) (z n) R v = 0 ↔ v = ψ v • u n) ∧
        ψ (Ring.inverse (repair (pencil (c n) R (z n)) w ψ)
          (deriv (pencil (c n) R) (z n) (u n))) ≠ 0) := by
  have hbase : pencil c₀ R z₀ u₀ = 0 :=
    (Packet06MaterialSector.pencil_kernel_actual c₀ hax₀ hmer₀ R hR hc₀ z₀ u₀).mpr hu₀
  have hA₀ : Differentiable ℂ (pencil c₀ R) :=
    fun z => (Packet06MaterialSector.pencil_analyticAt c₀ R hR z).differentiableAt
  have hAn : ∀ᶠ n in atTop, Differentiable ℂ (pencil (c n) R) :=
    Filter.Eventually.of_forall (fun n z => (Packet06MaterialSector.pencil_analyticAt (c n) R hR z).differentiableAt)
  have hscalar := Packet06SchurAnalytic.scalar_analyticAt (pencil c₀ R) w ψ z₀
    (Packet06MaterialSector.pencil_analyticAt c₀ R hR z₀) hunit
  obtain ⟨z,hz,hu,hgood⟩ := Packet06SchurModeLimit.convergent_kernel_modes
    (fun n => pencil (c n) R) (pencil c₀ R) u₀ w ψ z₀ _
    (Packet06MaterialSector.pencil_locally_uniform c c₀ D R hR hb hb₀ ha hc hc₀)
    hA₀ hAn hunit hbase hψ hscalar.differentiableAt.hasDerivAt hd
  let u : ℕ → Sector := fun n => Ring.inverse (repair (pencil (c n) R (z n)) w ψ) w
  refine ⟨z,u,hz,hu,?_⟩
  filter_upwards [hgood,hz.eventually_ne hz₀] with n hn hnz
  have hk := Packet06MaterialSector.pencil_kernel_actual (c n) (hax n) (hmer n) R hR (hc n) (z n)
  refine ⟨hnz,hn.1,(hk (u n)).mp hn.2.1,hn.2.2.1,?_,hn.2.2.2.2⟩
  intro v
  exact (hk v).symm.trans (hn.2.2.2.1 v)

end OQ14.Packet06ActualModePersistence
#print axioms OQ14.Packet06ActualModePersistence.actual_kernel_modes
