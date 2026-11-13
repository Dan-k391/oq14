import Packet06ScalarGaussLocalization

/-! Actual complex Maxwell modes supply the compact scalar transmission PDE.
The Gauss law and potential decomposition are derived from the volume kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06MaxwellScalarEquation
open MeasureTheory Metric Set Maxwell WeakCurl DivCurlCompact
  ConicalGradientGraph Packet05RegionalDivergence Packet06ScalarGaussLocalization
open scoped SchwartzMap
abbrev Space := Maxwell.Space
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev V := VectorFourier.VectorL2

def epsilon (c : Coefficient) (x : Space) : ℂ :=
  1+(c.value (VectorFourier.coordinateMap x) : ℂ)

theorem epsilon_memLp (c : Coefficient) : MemLp (epsilon c) ⊤ volume := by
  apply memLp_top_of_bound
    (measurable_const.add (Complex.measurable_ofReal.comp
      (c.measurable.comp VectorFourier.coordinateMap.measurable))).aestronglyMeasurable (1+c.bound)
  filter_upwards with x
  change ‖(1 : ℂ)+(c.value (VectorFourier.coordinateMap x) : ℂ)‖ ≤ 1+c.bound
  rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (by linarith [c.nonnegative (VectorFourier.coordinateMap x)])]
  linarith [c.bounded (VectorFourier.coordinateMap x)]

theorem actual_scalar_equation (c : Coefficient) (z : ℂ) (hz : z ≠ 0)
    (S : ℝ) (u : V)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x)=0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u=0)
    (χ : ContDiffBump (0 : Space)) :
    let U := Packet06ComplexConePotential.potentialData z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
    let W := Packet06ComplexPotential.correction z (DynamicVolume.source c u)
    let hW := Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
    CompactRepresentative (value χ U) ∧
    (∀ i, HasWeakPartial (value χ U) (gradient χ U i) i) ∧
    (∀ i, CompactRepresentative (correction χ W hW i)) ∧
    (∀ i, ∀ᵐ x ∂volume, x ∈ ball (0 : Space) χ.rIn →
      gradient χ U i x+correction χ W hW i x =
        Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u)
          (DynamicVolume.source c u) x i) ∧
    HasDivergenceOn (ball (0 : Space) χ.rIn) (flux χ U W hW (epsilon c) (epsilon_memLp c)) 0 := by
  dsimp only
  let U := Packet06ComplexConePotential.potentialData z S (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
  let W := Packet06ComplexPotential.correction z (DynamicVolume.source c u)
  let hW := Packet06ComplexPotential.correction_continuous z S (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
  have hGauss (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) χ.rIn) :
      (∑ i : Fin 3, ∫ x, epsilon c x*(U.derivative i x+W x i)*dcoord f x i)=0 := by
    let T := max |S| (max χ.rIn 0)
    have hST : S ≤ T := (le_abs_self S).trans (le_max_left _ _)
    have hplus : 0 ≤ T+S := by
      have ht : |S| ≤ T := le_max_left _ _
      linarith [neg_abs_le S]
    have hsupport : tsupport (f : Space → ℂ) ⊆ closedBall (0 : Space) T := by
      intro x hx
      have hh : ‖x‖ < χ.rIn := by simpa using hf hx
      have ht : χ.rIn ≤ T := (le_max_left _ _).trans (le_max_right _ _)
      simpa only [mem_closedBall,dist_zero_right] using hh.le.trans ht
    have hfc : HasCompactSupport (f : Space → ℂ) :=
      (isCompact_closedBall (0 : Space) T).of_isClosed_subset (isClosed_tsupport _) hsupport
    have h := Packet06ComplexGauss.electric_gauss c z hz S T hST hplus u hc hu ⟨f,hfc⟩ hsupport
    simpa only [epsilon,U,W,Packet06ComplexConePotential.potentialData,sub_add_cancel,
      DynamicSource.testPartial,GradientProjection.pderivative_apply] using h
  have h := compact_scalar_equation χ U W hW (epsilon c) (epsilon_memLp c) hGauss
  simpa only [U,W,Packet06ComplexConePotential.potentialData,sub_add_cancel] using h

end OQ14.Packet06MaxwellScalarEquation
#print axioms OQ14.Packet06MaxwellScalarEquation.epsilon_memLp
#print axioms OQ14.Packet06MaxwellScalarEquation.actual_scalar_equation
