import Packet06ExcitationTail
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SelectedExcitation
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
  OQ14.Packet06ConcreteModalGeometry OQ14.Packet06ConcreteModalBranch OQ14.Packet06SectorOperator
open OQ14.Packet06SimpleCertificate (Certified)
open scoped Topology
abbrev V := VectorFourier.VectorL2

theorem selected_from_branch {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (z₀ a₀ : ℂ) (hz₀ : z₀ ≠ 0) (hdet : ModalAlgebra.tmDet 1 (n : ℂ) z₀=0)
    (hfield : ∀ i, Packet06SphereLocalField.inner n z₀ a₀ (g.center i) 2 ≠ 0)
    (z : ℕ → ℂ) (v : ℕ → Sector) (hz : Tendsto z atTop (𝓝 z₀))
    (hv : Tendsto v atTop (𝓝 (a₀ • numerator n hn z₀)))
    (hresponse : Tendsto (fun j => Packet06LocalPencil.response (family n hn g j) (z j) 1 1 (v j)) atTop
      (𝓝 (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z₀ 1 1
        (a₀ • (numerator n hn z₀ : V)))))
    (P : ℕ → Prop) (hgood : ∀ᶠ j in atTop, z j ≠ 0 ∧ Certified (family n hn g j) 1 (z j) (v j) ∧ P j) :
    ∃ (j : ℕ) (p : ConicalStaticVolume.Data)
      (hp : p.cutoff = g.datum.cutoff ∧ p.contrast = eta j ∧ p.threshold = (3/4 : ℝ) ∧ p.exponent < 1)
      (s : Fin N → System p g.radius),
      Certified (family n hn g j) 1 (z j) (v j) ∧ P j ∧
      (∀ i k, ∀ᵐ x : Maxwell.Space, x ∈ ball 0 g.radius →
        totalCoordinate (s i) k x = Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (family n hn g j) (v j)) (DynamicVolume.source (family n hn g j) (v j))
          (x+g.center i) k) ∧
      ∀ i, ConicalIntrinsicCoefficient.coefficient (s i) g.radius_pos
        (by rw [hp.1]; exact g.radius_inner) hp.2.2.2 ≠ 0 := by
  obtain ⟨hax,hmer,hsupp⟩ := admissible g
  obtain ⟨hb,_,_,_,_,_⟩ := Packet06SphereInsertion.admissible n hn (cone g) hax hmer hsupp eta
    (fun j => (eta_bounds j).1.le) (fun j => (eta_bounds j).2) eta_tendsto
  let D := (ModalWeightedMode.coefficient n hn).bound+(cone g).bound
  have hD : 0 ≤ D := add_nonneg (StaticCoefficient.bound_nonnegative _) (StaticCoefficient.bound_nonnegative _)
  have hv' : Tendsto (fun j => (v j : V)) atTop (𝓝 (a₀ • (numerator n hn z₀ : V))) := by
    exact continuous_subtype_val.continuousAt.tendsto.comp hv
  obtain ⟨J,Z,L,hL,hP,hZ,hsource⟩ := Packet06ExcitationTail.uniform_tail (family n hn g) D hD hb
    z z₀ hz (fun j => (v j : V)) (a₀ • (numerator n hn z₀ : V)) hv'
    (fun j => z j ≠ 0 ∧ Certified (family n hn g j) 1 (z j) (v j) ∧ P j) hgood
  let η : ℕ → ℝ := fun j => eta (j+J)
  let zz : ℕ → ℂ := fun j => z (j+J)
  let uu : ℕ → V := fun j => v (j+J)
  have hη0 : Tendsto η atTop (𝓝 0) := eta_tendsto.comp (tendsto_add_atTop_nat J)
  have hη (j : ℕ) : 0 < η j := (eta_bounds (j+J)).1
  have hηb (j : ℕ) : η j ≤ 1 := (eta_bounds (j+J)).2
  have hzz (j : ℕ) : zz j ≠ 0 := (hP j).1
  have hker (j : ℕ) : ComplexConvolutionAnalytic.volumeBlock
      (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (zz j) 1 (uu j) = 0 := by
    have h := (hP j).2.1
    obtain ⟨w,ψ,_,hk,_,_⟩ := h
    exact hk
  have hresp : Tendsto (fun j => ComplexExteriorResponse.response
      (Packet06SphereInsertion.family n hn (cone g) η (fun j => (hη j).le) j) (zz j) 1 1 (uu j)) atTop
      (𝓝 (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z₀ 1 1
        (a₀ • (numerator n hn z₀ : V)))) := by
    simpa only [Packet06LocalPencil.response_actual] using hresponse.comp (tendsto_add_atTop_nat J)
  obtain ⟨p,hp,s,hactual,hnonzero⟩ := Packet06ConcreteExcitation.concrete_eventual n hn g η hη hη0 hηb
    zz uu hzz hker z₀ a₀ hz₀ hdet hfield hresp Z L hZ hL hsource
  obtain ⟨k,hk⟩ := hnonzero.exists
  refine ⟨k+J,p k,?_,s k,(hP k).2.1,(hP k).2.2,?_,?_⟩
  · simpa only [η] using hp k
  · exact hactual k
  · exact hk
#print axioms OQ14.Packet06SelectedExcitation.selected_from_branch
end OQ14.Packet06SelectedExcitation
