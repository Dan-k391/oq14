import Packet06ActualModePersistence
import Packet06MaterialPole

/-! Persistence of actual inverse poles and their physical electric residues,
on the same frequency and kernel branch furnished by material convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ModePolePersistence
open Filter Set Metric MeasureTheory Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
open StaticCoefficient (Coefficient)
open Packet06MaterialSector (pencil)
open scoped Topology

def SimpleObservedPole (c : Coefficient) (S : ℝ) (z : ℂ) (u : Sector) : Prop :=
  ∃ φ : Sector →L[ℂ] ℂ, φ (deriv (pencil c S) z u) ≠ 0 ∧
    ∀ T : ℝ, S ≤ T →
    ∃ (R : Sector →L[ℂ] VectorL2) (B : ℂ → Sector →L[ℂ] VectorL2),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, R x = (φ x / φ (deriv (pencil c S) z u)) • Packet06LocalPencil.response c z S T u) ∧
      Tendsto (fun v => (v-z) • (Packet06MaterialPole.observation c S T v).comp
        (Ring.inverse (pencil c S v))) (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ v in 𝓝[≠] z, (Packet06MaterialPole.observation c S T v).comp
        (Ring.inverse (pencil c S v)) = (v-z)⁻¹ • R + B v)

theorem repair_units_along {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : ℕ → ℂ → E →L[ℂ] E) (A₀ : ℂ → E →L[ℂ] E)
    (hA : TendstoLocallyUniformlyOn A A₀ atTop univ) (hA₀ : Continuous A₀)
    (w : E) (ψ : E →L[ℂ] ℂ) (z : ℕ → ℂ) (z₀ : ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (hunit : IsUnit (repair (A₀ z₀) w ψ)) :
    ∀ᶠ n in atTop, IsUnit (repair (A n (z n)) w ψ) := by
  have hwithin : Tendsto z atTop (𝓝[univ] z₀) := by simpa using hz
  have ht := hA.tendsto_comp hA₀.continuousWithinAt (mem_univ z₀) hwithin
  have hrepair : Tendsto (fun n => repair (A n (z n)) w ψ) atTop (𝓝 (repair (A₀ z₀) w ψ)) :=
    ht.add tendsto_const_nhds
  exact hrepair.eventually (Units.isOpen.mem_nhds hunit)

theorem actual_mode_poles (c : ℕ → Coefficient) (c₀ : Coefficient) (D S : ℝ)
    (hS : 0 ≤ S) (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (hc : ∀ (n : ℕ) (x : FourierL2.Space), x ∉ closedBall 0 S → (c n).value (VectorFourier.coordinateMap x) = 0)
    (hc₀ : ∀ x : FourierL2.Space, x ∉ closedBall 0 S → c₀.value (VectorFourier.coordinateMap x) = 0)
    (hax : ∀ n, Packet06MaterialSymmetry.Axial (c n))
    (hmer : ∀ n, Packet06MaterialSymmetry.Meridional (c n))
    (hax₀ : Packet06MaterialSymmetry.Axial c₀) (hmer₀ : Packet06MaterialSymmetry.Meridional c₀)
    (z₀ : ℂ) (hz₀ : z₀ ≠ 0) (u₀ w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hunit : IsUnit (repair (pencil c₀ S z₀) w ψ))
    (hu₀ : ComplexConvolutionAnalytic.volumeBlock c₀ z₀ S u₀ = 0) (hψ : ψ u₀ = 1)
    (hd : deriv (fun z => scalar (pencil c₀ S z) w ψ) z₀ ≠ 0) :
    ∃ (z : ℕ → ℂ) (u : ℕ → Sector),
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto u atTop (𝓝 u₀) ∧
      (∀ᶠ n in atTop, z n ≠ 0 ∧ u n ≠ 0 ∧
        ComplexConvolutionAnalytic.volumeBlock (c n) (z n) S (u n) = 0 ∧ ψ (u n) = 1 ∧
        (∀ v : Sector, ComplexConvolutionAnalytic.volumeBlock (c n) (z n) S v = 0 ↔ v = ψ v • u n) ∧
        SimpleObservedPole (c n) S (z n) (u n)) := by
  obtain ⟨z,u,hz,hu,hgood⟩ := Packet06ActualModePersistence.actual_kernel_modes c c₀ D S hS hb hb₀
    ha hc hc₀ hax hmer hax₀ hmer₀ z₀ hz₀ u₀ w ψ hunit hu₀ hψ hd
  have hAn := Packet06MaterialSector.pencil_locally_uniform c c₀ D S hS hb hb₀ ha hc hc₀
  have hA₀ : Continuous (pencil c₀ S) := continuous_iff_continuousAt.mpr
    (fun v => (Packet06MaterialSector.pencil_analyticAt c₀ S hS v).continuousAt)
  have hrep := repair_units_along (fun n => pencil (c n) S) (pencil c₀ S) hAn hA₀ w ψ z z₀ hz hunit
  refine ⟨z,u,hz,hu,?_⟩
  filter_upwards [hgood,hrep] with n hn hr
  refine ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,?_⟩
  refine ⟨ψ.comp (Ring.inverse (repair (pencil (c n) S (z n)) w ψ)),hn.2.2.2.2.2,?_⟩
  intro T hT
  exact Packet06MaterialPole.actual_observed_expansion (c n) (hax n) (hmer n) S T hS hT
    (hc n) (z n) (u n) w ψ hr hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.2

end OQ14.Packet06ModePolePersistence
#print axioms OQ14.Packet06ModePolePersistence.repair_units_along
#print axioms OQ14.Packet06ModePolePersistence.actual_mode_poles
