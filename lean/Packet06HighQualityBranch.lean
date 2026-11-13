import Packet06SphereInsertionPole
import Packet06PoleScale
import Packet06NormalizationLimit

/-! Actual high-Q physically normalized outgoing modes for fixed symmetric
positive-contrast insertions. Conical excitation is a separate assertion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06HighQualityBranch
open Filter Metric MeasureTheory Packet06SectorOperator Packet06PhysicalNormalization
open scoped Topology

theorem quality_stable (z : ℕ → ℂ) (z₀ : ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (Q : ℝ) (hre : 0 < z₀.re) (him : z₀.im < 0) (hQ : Q < z₀.re / (-2*z₀.im)) :
    ∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re / (-2*(z j).im) := by
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hz
  have hi := Complex.continuous_im.continuousAt.tendsto.comp hz
  have hq := hr.div (hi.const_mul (-2)) (by nlinarith : -2*z₀.im ≠ 0)
  filter_upwards [hr.eventually (Ioi_mem_nhds hre),hi.eventually (Iio_mem_nhds him),
    hq.eventually (Ioi_mem_nhds hQ)] with j hjr hji hjq
  exact ⟨hjr,hji,hjq⟩

theorem normalized_inserted_highQ (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
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
        (𝓝 (a₀ • Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z₀ 1 T (numerator n hn z₀)))) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re / (-2*(z j).im) ∧
        v j ≠ 0 ∧ ComplexConvolutionAnalytic.volumeBlock (c j) (z j) 1 (v j) = 0 ∧
        reciprocalNorm (c j) 1 (z j) (v j) = 1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (c j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (c j) 1 (z j) (v j)) := by
  dsimp only
  let c := Packet06SphereInsertion.family n hn cone η hη
  obtain ⟨z₀,hz₀,hdet,_,hre,him,hquality⟩ := ModalAsymptotics.tm_high_quality_zeros 1 n hn 0 Q hQ
  obtain ⟨ψ,z,u,_,hz,hu,hresponse,hN,hgood⟩ :=
    Packet06SphereInsertionPole.fixed_contrast_pole_persistence n hn hna z₀ hz₀ hdet cone hax hmer hsupp η hη hηb ht
  let N₀ := reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z₀ (numerator n hn z₀)
  have hN₀ : N₀ ≠ 0 :=
    Packet06PhysicalNormalization.reciprocalNorm_nonzero _ 1 (by norm_num) z₀ hz₀ _
      (ModalVolumeNormalization.numerator_pairing_nonzero n hn z₀ hz₀ hdet
        (Packet06SpherePole.determinant_simple n hn hna z₀ hz₀ hdet))
  obtain ⟨a₀,ha₀,ha₂,_⟩ := Packet06PhysicalScale.physical_unit_scale
    (ModalWeightedMode.coefficient n hn) 1 (by norm_num) z₀ (numerator n hn z₀) hN₀
  have hunit₀ : a₀^2*N₀ = 1 := by rw [ha₂]; exact inv_mul_cancel₀ hN₀
  obtain ⟨a,ha,hane,hunit⟩ := Packet06NormalizationLimit.compatible_scales
    (fun j => reciprocalNorm (c j) 1 (z j) (u j)) N₀ a₀ hN hN₀ hunit₀
  let v : ℕ → Sector := fun j => a j • u j
  have hqual := quality_stable z z₀ hz Q hre him hquality
  obtain ⟨_,_,_,hc,_,_⟩ := Packet06SphereInsertion.admissible n hn cone hax hmer hsupp η hη hηb ht
  refine ⟨z₀,a₀,z,v,hz₀,ha₀,hdet,hre,him,hquality,hz,ha.smul hu,?_,?_⟩
  · intro T hT
    have he := ha.smul (hresponse T hT)
    change Tendsto (fun j => Packet06LocalPencil.response (c j) (z j) 1 T (a j • (u j : Packet06SectorOperator.VectorL2))) _ _
    simpa only [map_smul] using he
  · filter_upwards [hgood,hunit,hqual] with j hj hNj hQj
    have hv : v j ≠ 0 := smul_ne_zero (hane j) hj.2.1
    have hvV : (v j : Packet06SectorOperator.VectorL2) ≠ 0 := fun h => hv (Subtype.ext h)
    have hk : ComplexConvolutionAnalytic.volumeBlock (c j) (z j) 1 (v j) = 0 := by
      change ComplexConvolutionAnalytic.volumeBlock (c j) (z j) 1 (a j • (u j : Packet06SectorOperator.VectorL2)) = 0
      rw [map_smul,hj.2.2.1,smul_zero]
    have hnorm : reciprocalNorm (c j) 1 (z j) (v j) = 1 := by
      change reciprocalNorm (c j) 1 (z j) (a j • (u j : Packet06SectorOperator.VectorL2)) = 1
      rw [Packet06PhysicalScale.reciprocalNorm_scale _ 1 (by norm_num)]
      exact hNj
    exact ⟨hQj.1,hQj.2.1,hQj.2.2,hv,hk,hnorm,
      Packet06OutgoingMode.actual_outgoing_mode (c j) (z j) 1 (by norm_num) (v j) (hc j) hk hvV,
      Packet06PoleScale.observed_pole_scale (c j) 1 (z j) (u j) (a j) (hane j) hj.2.2.2.2.2.2⟩

end OQ14.Packet06HighQualityBranch
#print axioms OQ14.Packet06HighQualityBranch.quality_stable
#print axioms OQ14.Packet06HighQualityBranch.normalized_inserted_highQ
