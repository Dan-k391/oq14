import Packet06SimpleCertificate

/-! Reusable simple-kernel certificates along actual material perturbations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06CertifiedPersistence
open Filter Set Metric MeasureTheory Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
open StaticCoefficient (Coefficient)
open Packet06MaterialSector (pencil)
open Packet06SimpleCertificate (Certified)
open scoped Topology

theorem actual_certified_modes (c : ℕ → Coefficient) (c₀ : Coefficient) (D S : ℝ)
    (hS : 0 ≤ S) (hb : ∀ j, (c j).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun j => (c j).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (j : ℕ) (x : FourierL2.Space), x ∉ closedBall 0 S → (c j).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : FourierL2.Space, x ∉ closedBall 0 S → c₀.value (VectorFourier.coordinateMap x) = 0)
    (hax : ∀ j, Packet06MaterialSymmetry.Axial (c j))
    (hmer : ∀ j, Packet06MaterialSymmetry.Meridional (c j))
    (hax₀ : Packet06MaterialSymmetry.Axial c₀) (hmer₀ : Packet06MaterialSymmetry.Meridional c₀)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (u₀ : Sector) (hcert : Certified c₀ S z₀ u₀) :
    ∃ (z : ℕ → ℂ) (u : ℕ → Sector),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto u atTop (𝓝 u₀) ∧
      (∀ᶠ j in atTop, z j ≠ 0 ∧ Certified (c j) S (z j) (u j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (c j) S (z j) (u j)) := by
  obtain ⟨w,ψ,hunit,hker,hψ,hd⟩ := hcert
  obtain ⟨z,u,hz,hu,hgood⟩ := Packet06ActualModePersistence.actual_kernel_modes
    c c₀ D S hS hb hb₀ ha hc hc₀ hax hmer hax₀ hmer₀ z₀ hz₀ u₀ w ψ hunit hker hψ hd
  have hAn := Packet06MaterialSector.pencil_locally_uniform c c₀ D S hS hb hb₀ ha hc hc₀
  have hA₀ : Continuous (pencil c₀ S) := continuous_iff_continuousAt.mpr
    (fun v => (Packet06MaterialSector.pencil_analyticAt c₀ S hS v).continuousAt)
  have hrep := Packet06ModePolePersistence.repair_units_along
    (fun j => pencil (c j) S) (pencil c₀ S) hAn hA₀ w ψ z z₀ hz hunit
  refine ⟨z,u,hz,hu,?_⟩
  filter_upwards [hgood,hrep] with j hj hr
  have hk := (Packet06MaterialSector.pencil_kernel_actual (c j) (hax j) (hmer j) S hS (hc j) (z j) (u j)).mpr hj.2.2.1
  have hi := repaired_inverse_vector (pencil (c j) S (z j)) (u j) w ψ hr hk hj.2.2.2.1
  have hder := Packet06SchurAnalytic.scalar_hasDerivAt (pencil (c j) S)
    (deriv (pencil (c j) S) (z j)) w ψ (z j)
    (Packet06MaterialSector.pencil_analyticAt (c j) S hS (z j)).differentiableAt.hasDerivAt hr
  have hdj : deriv (fun v => scalar (pencil (c j) S v) w ψ) (z j) ≠ 0 := by
    rw [hder.deriv,hi]
    exact hj.2.2.2.2.2
  refine ⟨hj.1,⟨w,ψ,hr,hj.2.2.1,hj.2.2.2.1,hdj⟩,?_⟩
  refine ⟨ψ.comp (Ring.inverse (repair (pencil (c j) S (z j)) w ψ)),hj.2.2.2.2.2,?_⟩
  intro T hT
  exact Packet06MaterialPole.actual_observed_expansion (c j) (hax j) (hmer j) S T hS hT
    (hc j) (z j) (u j) w ψ hr hj.2.2.1 hj.2.2.2.1 hj.2.2.2.2.2

end OQ14.Packet06CertifiedPersistence
#print axioms OQ14.Packet06CertifiedPersistence.actual_certified_modes
