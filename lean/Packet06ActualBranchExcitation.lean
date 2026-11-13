import Packet06CenteredBall
import Packet06ActualConeHolder
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet06ActualBranchExcitation
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

theorem eventual_nonzero (c : ℕ → Coefficient) (z : ℕ → ℂ) (u : ℕ → V)
    (hz : ∀ j, z j ≠ 0) (hker : ∀ j, ComplexConvolutionAnalytic.volumeBlock (c j) (z j) 1 (u j) = 0)
    (hc : ∀ j x, x ∉ closedBall 0 1 → (c j).value (VectorFourier.coordinateMap x) = 0)
    (p : ℕ → ConicalStaticVolume.Data) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (htp : ∀ j, (p j).threshold = t) (hell : Tendsto (fun j => (p j).eigenvalue) atTop (𝓝 2))
    (hd : Tendsto (fun j => (p j).contrast) atTop (𝓝 0)) (D : ℝ) (hD : 0 ≤ D)
    (hdb : ∀ j, (p j).contrast ≤ D) (hν : ∀ j, (p j).exponent < 1)
    (hhalf : ∀ᶠ j in atTop, (1/2 : ℝ) ≤ (p j).exponent)
    (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (hbi : ∀ j, b < (p j).cutoff.rIn)
    (center : Maxwell.Space) (hball : ∀ x ∈ closedBall (0 : Maxwell.Space) b, x+center ∈ ball 0 1)
    (hcontain : closedBall center b ⊆ closedBall (0 : Maxwell.Space) 1)
    (α : ℝ) (hα : α ≠ 0)
    (hmatch : ∀ j y, y ∈ ball (0 : Maxwell.Space) b → 1+(c j).value (VectorFourier.coordinateMap (y+center)) =
      α * ConicalLocalGauss.epsilon (p j) y)
    (Z L : ℝ) (hZ : ∀ j, ‖z j‖ ≤ Z) (hL : 0 ≤ L)
    (hsource : ∀ j i, ‖NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier (c j) (u j)) i‖ ≤ L)
    (F₀ : V) (hresponse : Tendsto (fun j => ComplexExteriorResponse.response (c j) (z j) 1 1 (u j)) atTop (𝓝 F₀))
    (F : Field) (hF : ∀ i, Continuous (fun x => F x i))
    (hbase : ∀ i, (Packet06CenteredBall.restrict b center F₀ i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 b)]
      fun x => F (center+x) i)
    (A : ℂ) (hA : A ≠ 0) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hclose : ∀ r : ℝ, |r| < R₀ → ‖Packet06SphereProjection.average F center r-A‖ < ‖A‖/2) :
    ∀ᶠ j in atTop, ConicalIntrinsicCoefficient.coefficient
      (Packet06ComplexConeSystem.system (c j) (z j) (hz j) 1 1 (by norm_num) (by norm_num) (u j) (hc j) (hker j)
        (p j) b (hbi j) center α hα hcontain (fun y hy => hmatch j y hy)) hb (hbi j) (hν j) ≠ 0 := by
  let ballContain : closedBall center b ⊆ closedBall (0 : Maxwell.Space) 1 := hcontain
  let sys : ∀ j, System (p j) b := fun j => Packet06ComplexConeSystem.system
    (c j) (z j) (hz j) 1 1 (by norm_num) (by norm_num) (u j) (hc j) (hker j)
      (p j) b (hbi j) center α hα ballContain (hmatch j)
  let g : ℕ → ConicalRungeBall.BallL2 b := fun j => Packet06CenteredBall.restrict b center
    (ComplexExteriorResponse.response (c j) (z j) 1 1 (u j))
  let g₀ := Packet06CenteredBall.restrict b center F₀
  have hg : Tendsto g atTop (𝓝 g₀) := Packet06CenteredBall.restrict_tendsto b center _ F₀ hresponse
  have hactual (j : ℕ) (i : Fin 3) : (g j i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 b)] totalCoordinate (sys j) i := by
    have ha := Packet06ComplexConeSystem.system_actual (c j) (z j) (hz j) 1 1 (by norm_num) (by norm_num)
      (u j) (hc j) (hker j) (p j) b (hbi j) center α hα ballContain (hmatch j) i
    have hf := Packet06CenteredBall.restrict_response_actual b center (c j) (z j) 1 1 (u j) (hc j)
      (fun x hx => ball_subset_closedBall (hball x hx)) i
    have hne : ∀ᵐ x : Maxwell.Space, dist x 0 ≠ b := by
      have hn : (volume : Measure Maxwell.Space) (sphere 0 b) = 0 := Measure.addHaar_sphere volume 0 b
      simpa only [ae_iff,ne_eq,not_not,sphere] using hn
    filter_upwards [hf,ae_restrict_of_ae ha,ae_restrict_mem measurableSet_closedBall,ae_restrict_of_ae hne] with x hf ha hx hne'
    have hx' : x ∈ ball (0 : Maxwell.Space) b := by
      have hle : dist x 0 ≤ b := hx
      exact lt_of_le_of_ne hle hne'
    exact hf.trans (ha hx').symm
  have hcenter : ‖center‖ ≤ 1 := by
    have h0 : (0 : Maxwell.Space) ∈ closedBall 0 b := by simpa using hb.le
    have h : ‖center‖ < 1 := by simpa using hball 0 h0
    exact h.le
  have hins : ∀ x ∈ closedBall (0 : Maxwell.Space) b, ‖x+center‖ ≤ 1 := by
    intro x hx
    have h : ‖x+center‖ < 1 := by simpa using hball x hx
    exact h.le
  let M := Z^2*L*Packet06GreenHolderEndpoint.constant Z 1 1
  have hM : 0 ≤ M := by dsimp [M]; exact mul_nonneg (mul_nonneg (sq_nonneg Z) hL) (Real.sqrt_nonneg _)
  have hW : ∀ j i x, x ∈ closedBall (0 : Maxwell.Space) b →
      ‖(sys j).correction i x-(sys j).correction i 0‖ ≤ M*‖x‖^(1/2 : ℝ) := by
    intro j
    exact Packet06ActualConeHolder.correction_holder (c j) (z j) (hz j) 1 1 (by norm_num) (by norm_num)
      (u j) (hc j) (hker j) (p j) b hb.le (hbi j) hb1 center α hα ballContain (hmatch j)
      Z 1 L (hZ j) (by norm_num) (by norm_num) hL hcenter hins (hsource j)
  exact Packet06ModeExcitation.eventual_actual_excitation p (fun j => (p j).eigenvalue)
    (fun j => (p j).contrast) (fun _ => rfl) (fun _ => rfl) t ht ht1 htp hell hd
    (fun j => (p j).eigenvalue_bounds) D hD (fun j => ⟨(p j).contrast_nonnegative,hdb j⟩)
    hν hhalf b hb hbi M (1/2) hM (by norm_num) sys hW g g₀ hg hactual F hF center hbase A hA R₀ hR₀ hclose
#print axioms OQ14.Packet06ActualBranchExcitation.eventual_nonzero
end OQ14.Packet06ActualBranchExcitation
