import Packet06ExternalLeft
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ExternalCanonical
open Filter Metric Packet06SectorOperator Packet06MaterialSector Packet06ExternalLeft
open Packet06ExternalResidue Packet06RankOneRepair Packet06ScalarSchur Packet06SchurAnalytic
open Packet06PhysicalNormalization KernelReciprocity
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev BallL2 := ConicalRungeBall.BallL2

theorem selected_physical_left_residue (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0)
    (hN : reciprocalNorm c S z u = 1) :
    ∃ R : VectorL2 →L[ℂ] BallL2 T,
      (∀ f, R f = (physicalLeft c u (incidentDatum c S J z f) /
        vectorPair (deriv (fun v => ComplexConvolutionAnalytic.volumeBlock c v S) z u) u) •
          ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u)) ∧
      Tendsto (fun v => (v-z) • selectedScattered c S J T v) (𝓝[≠] z) (𝓝 R) := by
  let A := pencil c S
  let φ : Sector →L[ℂ] ℂ := ψ.comp (Ring.inverse (repair (A z) w ψ))
  have hA : AnalyticAt ℂ A z := pencil_analyticAt c S hS z
  have hk : A z u = 0 := (pencil_kernel_actual c ha hm S hS hc z u).mpr hu
  have hrep : Ring.inverse (repair (A z) w ψ) w = u :=
    repaired_inverse_vector (A z) u w ψ hC hk hψ
  have hder := scalar_hasDerivAt A (deriv A z) w ψ z hA.differentiableAt.hasDerivAt hC
  have hcross : deriv (fun v => scalar (A v) w ψ) z ≠ 0 := by
    rw [hder.deriv,hrep]
    exact hd
  have hd' : ψ (Ring.inverse (repair (A z) w ψ)
      (deriv A z (Ring.inverse (repair (A z) w ψ) w))) ≠ 0 := by
    rw [hrep]
    exact hd
  have hunits := Packet06SchurPole.punctured_units A w ψ z _ hA hC hder hd'
  obtain ⟨R₀,B,_,hB,hform,_,hexp⟩ :=
    Packet06MaterialPole.actual_inverse_expansion c ha hm S hS hc z u w ψ hC hu hψ hd
  have hconst := Packet06Cokernel.laurent_constant_identity A (deriv A z) z R₀ B
    hA.differentiableAt.hasDerivAt hB hunits hexp
  have hleft : physicalLeft c u (deriv A z u) ≠ 0 := by
    rw [physicalLeft_crossing c ha hm S hS hc z u]
    intro hz
    have hn := reciprocalNorm_eq_crossing c S hS z (u : VectorL2)
    rw [hN,hz,mul_zero] at hn
    exact one_ne_zero hn
  have hratio (v : Sector) : φ v / φ (deriv A z u) =
      physicalLeft c u v / physicalLeft c u (deriv A z u) :=
    left_ratio (A z) (deriv A z) (B z) R₀ φ (physicalLeft c u) u hleft
      (physicalLeft_annihilates c ha hm S hS hc z u hu) hform hconst v
  obtain ⟨R,hR,hlim⟩ := selected_residue_limit c ha hm S J T hS hJ hST hc z u w ψ hC hu hψ hd
  refine ⟨R,?_,hlim⟩
  intro f
  rw [hR,hratio,physicalLeft_crossing c ha hm S hS hc z u]

#print axioms OQ14.Packet06ExternalCanonical.selected_physical_left_residue
end OQ14.Packet06ExternalCanonical
