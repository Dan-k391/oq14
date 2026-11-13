import Packet06ComplexGauss
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexConeSystem
open MeasureTheory Metric OQ14.Maxwell OQ14.DynamicSource
open scoped SchwartzMap
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev V := VectorFourier.VectorL2

def system (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S) (u : V)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0)
    (p : ConicalStaticVolume.Data) (b : ℝ) (hb : b < p.cutoff.rIn) (center : Space) (α : ℝ) (hα : α ≠ 0)
    (hball : closedBall center b ⊆ closedBall 0 T)
    (hmatch : ∀ y ∈ ball (0 : Space) b, 1+c.value (VectorFourier.coordinateMap (y+center)) =
      α * ConicalLocalGauss.epsilon p y) : ConicalProjectionData.System p b := by
  let F := StaticCoefficient.sqrtMultiplier c u
  let ρ := DynamicVolume.source c u
  have hs := DynamicVolume.source_zero c u S hc
  have hF := StaticNewton.material_source_ae c u
  let U := ConicalTranslatedPotential.translated center (Packet06ComplexConePotential.potentialData z S F ρ hs hF)
  let W : Field := fun x i => Packet06ComplexPotential.correction z ρ (x+center) i
  have hW (i : Fin 3) : Continuous (fun x => W x i) :=
    (Packet06ComplexPotential.correction_continuous z S F ρ hs hF i).comp (continuous_id.add continuous_const)
  apply ConicalProjectionLocalization.ofPotential p b hb U W hW
  intro f hf
  have h := Packet06ComplexGauss.centered_gauss c z hz S T hST hplus u hc hu p b center α hα hball hmatch f hf
  have he (i : Fin 3) : (∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ) *
      (U.derivative i x+W x i)*dcoord f x i) =
      ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
        Packet06ComplexElectric.electric z F ρ (x+center) i*dcoord f x i := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [U, ConicalTranslatedPotential.translated, Packet06ComplexConePotential.potentialData, W]
    ring
  simpa only [he] using h

theorem system_actual (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S) (u : V)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0)
    (p : ConicalStaticVolume.Data) (b : ℝ) (hb : b < p.cutoff.rIn) (center : Space) (α : ℝ) (hα : α ≠ 0)
    (hball : closedBall center b ⊆ closedBall 0 T)
    (hmatch : ∀ y ∈ ball (0 : Space) b, 1+c.value (VectorFourier.coordinateMap (y+center)) =
      α * ConicalLocalGauss.epsilon p y) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalProjectionData.totalCoordinate (system c z hz S T hST hplus u hc hu p b hb center α hα hball hmatch) i x =
        Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) (x+center) i := by
  let F := StaticCoefficient.sqrtMultiplier c u
  let ρ := DynamicVolume.source c u
  have hs := DynamicVolume.source_zero c u S hc
  have hF := StaticNewton.material_source_ae c u
  let U := ConicalTranslatedPotential.translated center (Packet06ComplexConePotential.potentialData z S F ρ hs hF)
  have ht := ConicalProjectionData.totalCoordinate_ae
    (system c z hz S T hST hplus u hc hu p b hb center α hα hball hmatch) i
  have hg := ConicalGradientGraph.gradient_ae p.cutoff U i
  filter_upwards [ht,hg] with x htx hgx
  intro hx
  have hm := ConicalGradientGraph.bump_inner p.cutoff x (ball_subset_ball hb.le hx)
  rw [htx]
  change ConicalGradientGraph.gradient p.cutoff U i x +
    ConicalGradientGraph.bump p.cutoff x * Packet06ComplexPotential.correction z ρ (x+center) i = _
  rw [hgx, hm.1, hm.2 i]
  dsimp [U, ConicalTranslatedPotential.translated, Packet06ComplexConePotential.potentialData]
  ring

#print axioms OQ14.Packet06ComplexConeSystem.system
#print axioms OQ14.Packet06ComplexConeSystem.system_actual
end OQ14.Packet06ComplexConeSystem
