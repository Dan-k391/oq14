import Packet06CertifiedSphere

/-! The same high-Q physical insertion branch retains the exact data needed
to continue it under a subsequent material rounding. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06CertifiedInsertion
open Filter Metric Packet06SectorOperator Packet06SimpleCertificate
open Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology

theorem normalized_certified_insertions (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (cone : StaticCoefficient.Coefficient)
    (hax : Packet06MaterialSymmetry.Axial cone) (hmer : Packet06MaterialSymmetry.Meridional cone)
    (hsupp : ∀ x : FourierL2.Space, x ∉ closedBall 0 1 → cone.value (VectorFourier.coordinateMap x) = 0)
    (η : ℕ → ℝ) (hη : ∀ j, 0 ≤ η j) (hηb : ∀ j, η j ≤ 1)
    (ht : Tendsto η atTop (𝓝 0)) (Q : ℝ) (hQ : 0 ≤ Q) :
    let c := Packet06SphereInsertion.family n hn cone η hη
    ∃ (z₀ a₀ : ℂ) (z : ℕ → ℂ) (v : ℕ → Sector),
      z₀ ≠ 0 ∧ a₀ ≠ 0 ∧ ModalAlgebra.tmDet 1 (n : ℂ) z₀ = 0 ∧
      0 < z₀.re ∧ z₀.im < 0 ∧ Q < z₀.re / (-2*z₀.im) ∧
      Tendsto z atTop (𝓝 z₀) ∧ Tendsto v atTop (𝓝 (a₀ • numerator n hn z₀)) ∧
      (∀ T : ℝ, 1 ≤ T → Tendsto
        (fun j => Packet06LocalPencil.response (c j) (z j) 1 T (v j)) atTop
        (𝓝 (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z₀ 1 T
          (a₀ • (numerator n hn z₀ : VectorL2))))) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re / (-2*(z j).im) ∧
        Certified (c j) 1 (z j) (v j) ∧ reciprocalNorm (c j) 1 (z j) (v j) = 1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (c j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (c j) 1 (z j) (v j)) := by
  dsimp only
  let c := Packet06SphereInsertion.family n hn cone η hη
  obtain ⟨z₀,a₀,hz₀,ha₀,hdet,hre,him,hquality,hcert,hN,_⟩ :=
    Packet06CertifiedSphere.physically_normalized_highQ_sphere n hn hna Q hQ
  obtain ⟨hb,hb₀,ha,hc,haxc,hmerc⟩ :=
    Packet06SphereInsertion.admissible n hn cone hax hmer hsupp η hη hηb ht
  obtain ⟨z,v,hz,hv,hresponse,hgood⟩ := Packet06CertifiedNormalization.physical_certified_modes
    c (ModalWeightedMode.coefficient n hn) ((ModalWeightedMode.coefficient n hn).bound+cone.bound)
    1 (by norm_num) hb hb₀ ha hc (ModalWeightedMode.coefficient_support n hn) haxc hmerc
    (Packet06SphereSymmetry.sphere_axial n hn) (Packet06SphereSymmetry.sphere_meridional n hn)
    z₀ hz₀ (a₀ • numerator n hn z₀) hcert hN
  have hqual := Packet06HighQualityBranch.quality_stable z z₀ hz Q hre him hquality
  refine ⟨z₀,a₀,z,v,hz₀,ha₀,hdet,hre,him,hquality,hz,hv,hresponse,?_⟩
  filter_upwards [hgood,hqual] with j hj hQj
  exact ⟨hQj.1,hQj.2.1,hQj.2.2,hj.2⟩

end OQ14.Packet06CertifiedInsertion
#print axioms OQ14.Packet06CertifiedInsertion.normalized_certified_insertions
