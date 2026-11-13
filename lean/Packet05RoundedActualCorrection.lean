import Packet05RoundedCorrectionBounds
import Packet05NestedCutoffSupport

/-! The uniform correction estimates apply to the exact compact correction
used by the Maxwell scalar equation, not only an existential representative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RoundedActualCorrection
open MeasureTheory Set Metric Filter Maxwell WeakCurl WeakPoynting DivCurlCompact
  Packet06ConcreteModalRounding
open scoped Topology
abbrev Space := Maxwell.Space

def actualCorrection {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (χ : ContDiffBump (0 : Space)) (j : ℕ) : Fin 3 → L2Scalar :=
  Packet06ScalarGaussLocalization.correction χ
    (Packet06ComplexPotential.correction (z j) (DynamicVolume.source (rounded n hn g η hη j) (v j)))
    (Packet06ComplexPotential.correction_continuous (z j) 1
      (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
      (DynamicVolume.source (rounded n hn g η hη j) (v j))
      (DynamicVolume.source_zero (rounded n hn g η hη j) (v j) 1
        (Packet05RoundedModeSupport.rounded_support n hn g η hη j))
      (StaticNewton.material_source_ae (rounded n hn g η hη j) (v j)))

theorem rounded_actual_correction {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (z₀ : ℂ) (v₀ : Packet06SectorOperator.Sector)
    (hz : Tendsto z atTop (𝓝 z₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (χ : ContDiffBump (0 : Space)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j k,
      ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
        (∀ i, HasWeakPartial (actualCorrection n hn g η hη z v χ j k) (D i) i) ∧
        (∀ i l, HasWeakPartial (D i) (T i l) l) ∧
        ‖actualCorrection n hn g η hη z v χ j k‖ ≤ C ∧
        (∀ i, ‖D i‖ ≤ C) ∧ (∀ i l, ‖T i l‖ ≤ C) ∧
        ∀ x, χ x=1 → ‖Packet06ComplexPotential.correction (z j)
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) x k‖ ≤
          10*Packet05ExplicitAnisotropicBound.universalConstant*C := by
  let ψ : Test := (Packet05NestedChartCutoffs.realTest χ).complexTest.toTest
  have hψ : ContDiff ℝ 2 ψ.function := Complex.ofRealCLM.contDiff.comp χ.contDiff
  have hψR : tsupport ψ.function ⊆ ball (0 : Space) (χ.rOut+1) := by
    have he : tsupport ψ.function=closedBall (0 : Space) χ.rOut :=
      (Packet05NestedCutoffSupport.complex_support (Packet05NestedChartCutoffs.realTest χ)).trans χ.tsupport_eq
    rw [he]
    exact closedBall_subset_ball (by linarith)
  obtain ⟨C,hC,hall⟩ := Packet05RoundedCorrectionBounds.rounded_family_correction n hn g η hη
    z v z₀ v₀ hz hv (χ.rOut+1) (by linarith [χ.rOut_pos]) ψ hψ hψR
  refine ⟨C,hC,?_⟩
  intro j k
  obtain ⟨U,D,T,hD,hT,hval,hUn,hDn,hTn,hpoint⟩ := hall j k
  have hval' : (U : Space → ℂ) =ᵐ[volume] (fun x => ψ.function x*
      Packet06ComplexPotential.correction (z j) (DynamicVolume.source (rounded n hn g η hη j) (v j)) x k) := hval
  have hactual : actualCorrection n hn g η hη z v χ j k=U := by
    apply Lp.ext
    exact (Packet06ScalarGaussLocalization.correction_ae χ _ _ k).trans hval'.symm
  rw [←hactual] at hD hUn
  refine ⟨D,T,hD,hT,hUn,hDn,hTn,?_⟩
  intro x hx
  exact hpoint x (by change (χ x : ℂ)=1; rw [hx,Complex.ofReal_one])

end OQ14.Packet05RoundedActualCorrection
#print axioms OQ14.Packet05RoundedActualCorrection.rounded_actual_correction
