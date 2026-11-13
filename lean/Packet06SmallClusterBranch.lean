import Packet06SmallClusterGeometry
import Packet06ConcreteModalBranch

/-! Cluster size can depend on the selected base frequency, before continuation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SmallClusterBranch
open Filter Metric Packet06SectorOperator Packet06ConcreteModalGeometry Packet06ConcreteModalBranch
open Packet06SimpleCertificate (Certified)
open Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology

theorem small_cluster_branch (N : ℕ) (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (Q : ℝ) (hQ : 0 ≤ Q)
    (δ : ℂ → ℝ) (hδ : ∀ z : ℂ, 0 < z.re → 0 < δ z) :
    ∃ (z₀ a₀ : ℂ) (g : Geometry N n) (z : ℕ → ℂ) (v : ℕ → Sector),
      z₀ ≠ 0 ∧ a₀ ≠ 0 ∧ ModalAlgebra.tmDet 1 (n : ℂ) z₀=0 ∧
      0 < z₀.re ∧ z₀.im < 0 ∧ Q < z₀.re/(-2*z₀.im) ∧
      (∀ i, closedBall (g.center i) g.datum.cutoff.rOut ⊆ ball 0 (δ z₀)) ∧
      (∀ i, Packet06SphereLocalField.inner n z₀ a₀ (g.center i) 2 ≠ 0) ∧
      Certified (ModalWeightedMode.coefficient n hn) 1 z₀ (a₀ • numerator n hn z₀) ∧
      reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z₀ (a₀ • numerator n hn z₀)=1 ∧
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 (a₀ • numerator n hn z₀)) ∧
      (∀ T : ℝ, 1 ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (family n hn g j) (z j) 1 T (v j)) atTop
        (𝓝 (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z₀ 1 T
          (a₀ • (numerator n hn z₀ : VectorL2))))) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Certified (family n hn g j) 1 (z j) (v j) ∧
        reciprocalNorm (family n hn g j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (family n hn g j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (family n hn g j) 1 (z j) (v j)) := by
  obtain ⟨z₀,a₀,hz₀,ha₀,hdet,hre,him,hquality,hcert,hN,_⟩ :=
    Packet06CertifiedSphere.physically_normalized_highQ_sphere n hn hna Q hQ
  obtain ⟨g,hcluster,hfield⟩ := Packet06SmallClusterGeometry.exists_geometry_in_ball
    N n hn z₀ a₀ hz₀ ha₀ (δ z₀) (hδ z₀ hre)
  obtain ⟨hax,hmer,hsupp⟩ := admissible g
  obtain ⟨hb,hb₀,ha,hc,haxc,hmerc⟩ :=
    Packet06SphereInsertion.admissible n hn (cone g) hax hmer hsupp eta
      (fun j => (eta_bounds j).1.le) (fun j => (eta_bounds j).2) eta_tendsto
  obtain ⟨z,v,hz,hv,hresponse,hgood⟩ := Packet06CertifiedNormalization.physical_certified_modes
    (family n hn g) (ModalWeightedMode.coefficient n hn)
    ((ModalWeightedMode.coefficient n hn).bound+(cone g).bound) 1 (by norm_num)
    hb hb₀ ha hc (ModalWeightedMode.coefficient_support n hn) haxc hmerc
    (Packet06SphereSymmetry.sphere_axial n hn) (Packet06SphereSymmetry.sphere_meridional n hn)
    z₀ hz₀ (a₀ • numerator n hn z₀) hcert hN
  have hqual := Packet06HighQualityBranch.quality_stable z z₀ hz Q hre him hquality
  refine ⟨z₀,a₀,g,z,v,hz₀,ha₀,hdet,hre,him,hquality,hcluster,hfield,hcert,hN,hz,hv,hresponse,?_⟩
  filter_upwards [hgood,hqual] with j hj hq
  exact ⟨hq.1,hq.2.1,hq.2.2,hj.2⟩

end OQ14.Packet06SmallClusterBranch
#print axioms OQ14.Packet06SmallClusterBranch.small_cluster_branch
