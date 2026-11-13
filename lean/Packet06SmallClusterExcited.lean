import Packet06SelectedExcitation
import Packet06SmallClusterBranch
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SmallClusterExcited
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
  OQ14.Packet06ConcreteModalGeometry OQ14.Packet06ConcreteModalBranch OQ14.Packet06SectorOperator
open OQ14.Packet06SimpleCertificate (Certified)
open OQ14.Packet06PhysicalNormalization (reciprocalNorm)
open scoped Topology
abbrev V := VectorFourier.VectorL2

theorem exists_excited_mode (N : ℕ) (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (Q : ℝ) (hQ : 0 ≤ Q) (ηmax ε : ℝ) (hηmax : 0 < ηmax) (hε : 0 < ε) (δ : ℂ → ℝ) (hδ : ∀ z : ℂ, 0 < z.re → 0 < δ z) :
    ∃ (z₀ a₀ : ℂ) (g : Geometry N n) (z : ℂ) (v : Sector) (η : ℝ) (hη : 0 < η)
      (p : ConicalStaticVolume.Data)
      (hp : p.cutoff=g.datum.cutoff ∧ p.contrast=η ∧ p.threshold=(3/4 : ℝ) ∧ p.exponent<1)
      (s : Fin N → System p g.radius),
      z₀ ≠ 0 ∧ a₀ ≠ 0 ∧ ModalAlgebra.tmDet 1 (n : ℂ) z₀=0 ∧
      0 < z₀.re ∧ z₀.im < 0 ∧ Q < z₀.re/(-2*z₀.im) ∧
      (∀ i, closedBall (g.center i) g.datum.cutoff.rOut ⊆ ball 0 (δ z₀)) ∧
      η < ηmax ∧ |z.re-z₀.re| < ε*z₀.re ∧
      0 < z.re ∧ z.im < 0 ∧ Q < z.re/(-2*z.im) ∧
      Certified (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) (cone g) η hη.le) 1 z v ∧
      reciprocalNorm (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) (cone g) η hη.le) 1 z v=1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) (cone g) η hη.le) z 1 v ∧
      Packet06ModePolePersistence.SimpleObservedPole (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) (cone g) η hη.le) 1 z v ∧
      (∀ i k, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 g.radius →
        totalCoordinate (s i) k x = Packet06ComplexElectric.electric z
          (StaticCoefficient.sqrtMultiplier (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) (cone g) η hη.le) v)
          (DynamicVolume.source (Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) (cone g) η hη.le) v)
          (x+g.center i) k) ∧
      ∀ i, ConicalIntrinsicCoefficient.coefficient (s i) g.radius_pos
        (by rw [hp.1]; exact g.radius_inner) hp.2.2.2 ≠ 0 := by
  obtain ⟨z₀,a₀,g,z,v,hz₀,ha₀,hdet,hre,him,hquality,hcluster,hfield,_hcert,_hN,hz,hv,hresponse,hgood⟩ :=
    Packet06SmallClusterBranch.small_cluster_branch N n hn hna Q hQ δ hδ
  let P : ℕ → Prop := fun j => eta j < ηmax ∧ |(z j).re-z₀.re| < ε*z₀.re ∧ 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
    reciprocalNorm (family n hn g j) 1 (z j) (v j)=1 ∧
    Packet06OutgoingMode.IsActualOutgoingMode (family n hn g j) (z j) 1 (v j) ∧
    Packet06ModePolePersistence.SimpleObservedPole (family n hn g j) 1 (z j) (v j)
  have hgood' : ∀ᶠ j in atTop, z j ≠ 0 ∧ Certified (family n hn g j) 1 (z j) (v j) ∧ P j := by
    have hηevent : ∀ᶠ j in atTop, eta j < ηmax := (tendsto_order.mp eta_tendsto).2 ηmax hηmax
    have hfreq : ∀ᶠ j in atTop, |(z j).re-z₀.re| < ε*z₀.re := by
      have hball := hz.eventually (Metric.ball_mem_nhds z₀ (mul_pos hε hre))
      filter_upwards [hball] with j hj
      have hh : ‖z j-z₀‖ < ε*z₀.re := by simpa only [mem_ball,dist_eq_norm] using hj
      exact (Complex.abs_re_le_norm (z j-z₀)).trans_lt (by simpa only [Complex.sub_re] using hh)
    filter_upwards [hgood,hηevent,hfreq] with j hj hηj hfj
    have hzj : z j ≠ 0 := by intro hzj; simp [hzj] at hj
    exact ⟨hzj,hj.2.2.2.1,hηj,hfj,hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.2⟩
  obtain ⟨j,p,hp,s,hcert,hP,hactual,hnonzero⟩ := Packet06SelectedExcitation.selected_from_branch n hn g
    z₀ a₀ hz₀ hdet hfield z v hz hv (hresponse 1 (by norm_num)) P hgood'
  refine ⟨z₀,a₀,g,z j,v j,eta j,(eta_bounds j).1,p,hp,s,hz₀,ha₀,hdet,hre,him,hquality,hcluster,?_⟩
  simpa only [P,family,Packet06SphereInsertion.family] using
    (show eta j < ηmax ∧ |(z j).re-z₀.re| < ε*z₀.re ∧ 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
      Certified (family n hn g j) 1 (z j) (v j) ∧
      reciprocalNorm (family n hn g j) 1 (z j) (v j)=1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode (family n hn g j) (z j) 1 (v j) ∧
      Packet06ModePolePersistence.SimpleObservedPole (family n hn g j) 1 (z j) (v j) ∧
      (∀ i k, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 g.radius →
        totalCoordinate (s i) k x = Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (family n hn g j) (v j)) (DynamicVolume.source (family n hn g j) (v j))
          (x+g.center i) k) ∧
      ∀ i, ConicalIntrinsicCoefficient.coefficient (s i) g.radius_pos
        (by rw [hp.1]; exact g.radius_inner) hp.2.2.2 ≠ 0 from
      ⟨hP.1,hP.2.1,hP.2.2.1,hP.2.2.2.1,hP.2.2.2.2.1,hcert,hP.2.2.2.2.2.1,hP.2.2.2.2.2.2.1,hP.2.2.2.2.2.2.2,hactual,hnonzero⟩)
#print axioms OQ14.Packet06SmallClusterExcited.exists_excited_mode
end OQ14.Packet06SmallClusterExcited
