import Packet06HighQualityBranch

/-! Arbitrarily small strictly positive fixed-profile insertions with actual
physically normalized high-Q outgoing modes and selected-sector poles. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06PositiveHighQuality
open Filter Metric Packet06SectorOperator
open scoped Topology

theorem positive_inserted_highQ (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (cone : StaticCoefficient.Coefficient)
    (hax : Packet06MaterialSymmetry.Axial cone) (hmer : Packet06MaterialSymmetry.Meridional cone)
    (hsupp : ∀ x : FourierL2.Space, x ∉ closedBall 0 1 → cone.value (VectorFourier.coordinateMap x) = 0)
    (Q : ℝ) (hQ : 0 ≤ Q) (ε : ℝ) (hε : 0 < ε) :
    ∃ (η : ℝ) (hη : 0 ≤ η) (z : ℂ) (v : Sector),
      let c := Packet06ContrastInsertion.addScaled (ModalWeightedMode.coefficient n hn) cone η hη
      0 < η ∧ η ≤ 1 ∧ η < ε ∧ 0 < z.re ∧ z.im < 0 ∧ Q < z.re / (-2*z.im) ∧
      v ≠ 0 ∧ ComplexConvolutionAnalytic.volumeBlock c z 1 v = 0 ∧
      Packet06PhysicalNormalization.reciprocalNorm c 1 z v = 1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode c z 1 v ∧
      Packet06ModePolePersistence.SimpleObservedPole c 1 z v := by
  let η : ℕ → ℝ := fun j => 1 / (j+1 : ℝ)
  have hpos (j : ℕ) : 0 < η j := by dsimp [η]; positivity
  have hnonneg (j : ℕ) : 0 ≤ η j := (hpos j).le
  have hbound (j : ℕ) : η j ≤ 1 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < j+1)).mpr
    have hj := Nat.cast_nonneg (α := ℝ) j
    linarith
  have ht : Tendsto η atTop (𝓝 0) := by
    simpa only [η] using tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨_,_,z,v,_,_,_,_,_,_,_,_,_,hgood⟩ :=
    Packet06HighQualityBranch.normalized_inserted_highQ n hn hna cone hax hmer hsupp η hnonneg hbound ht Q hQ
  have hsmall : ∀ᶠ j in atTop, η j < ε := ht.eventually (Iio_mem_nhds hε)
  obtain ⟨j,hj,hjε⟩ := (hgood.and hsmall).exists
  exact ⟨η j,hnonneg j,z j,v j,hpos j,hbound j,hjε,hj⟩

end OQ14.Packet06PositiveHighQuality
#print axioms OQ14.Packet06PositiveHighQuality.positive_inserted_highQ
