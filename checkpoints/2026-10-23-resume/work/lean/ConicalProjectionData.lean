import ConicalLocalGauss
import ConicalGraphEnergy
import PolarMomentContinuity

/-! Actual L2 potential gradient and continuous compact correction with a local smooth-test Gauss law. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalProjectionData
open MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalGradientGraph OQ14.PolarMomentTesting
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space

/-- These are first-order spatial data. No radial equation or expansion is included. -/
structure System (p : Data) (a : ℝ) where
  graph : Graph
  correction : Fin 3 → Space → ℂ
  continuous : ∀ i, Continuous (correction i)
  compact : ∀ i, HasCompactSupport (correction i)
  gauss : ∀ f : 𝓢(Space,ℂ), tsupport (f : Space → ℂ) ⊆ ball (0 : Space) a →
    (∑ i : Fin 3, ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
      (graph.gradient i x+correction i x)*dcoord f x i)=0

variable {p : Data} {a : ℝ}

theorem correction_memLp (s : System p a) (i : Fin 3) : MemLp (s.correction i) 2 (volume : Measure Space) :=
  (s.continuous i).memLp_of_hasCompactSupport (s.compact i)

def correctionL2 (s : System p a) (i : Fin 3) : WeakCurl.L2Scalar :=
  (correction_memLp s i).toLp (s.correction i)

theorem correctionL2_ae (s : System p a) (i : Fin 3) :
    (correctionL2 s i : Space → ℂ) =ᵐ[volume] s.correction i := (correction_memLp s i).coeFn_toLp

def totalCoordinate (s : System p a) (i : Fin 3) : WeakCurl.L2Scalar := s.graph.gradient i+correctionL2 s i

theorem totalCoordinate_ae (s : System p a) (i : Fin 3) :
    (totalCoordinate s i : Space → ℂ) =ᵐ[volume] fun x => s.graph.gradient i x+s.correction i x := by
  filter_upwards [Lp.coeFn_add (s.graph.gradient i) (correctionL2 s i),correctionL2_ae s i] with x ha hw
  change (s.graph.gradient i+correctionL2 s i) x=_
  rw [ha]
  simp only [Pi.add_apply,hw]

theorem actual_gauss_pairing (s : System p a) (hai : a < p.cutoff.rIn)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) a) :
    (∑ i : Fin 3, ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*totalCoordinate s i x*
      ConicalAnnularTests.angularDerivative p.eigenvalue p.threshold η x i)=0 := by
  apply ConicalLocalGauss.angular_gauss p a hai (totalCoordinate s) _ η hη hc hs
  intro f hf
  have he (i : Fin 3) : (∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*totalCoordinate s i x*dcoord f x i)=
      ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*(s.graph.gradient i x+s.correction i x)*dcoord f x i :=
    integral_congr_ae ((totalCoordinate_ae s i).mono (fun x hx => by dsimp only at hx ⊢; rw [hx]))
  simpa only [he] using s.gauss f hf

def radialCorrection (s : System p a) (r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (s.correction i) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i) r

def tangentCorrection (s : System p a) (r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (s.correction i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r

theorem radialCorrection_continuous (s : System p a) : Continuous (radialCorrection s) := by
  apply continuous_finset_sum
  intro i _
  obtain ⟨C,hC,hb⟩ := ConicalMomentWeights.radial_bound _ _ _ p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact PolarMomentContinuity.moment_continuous _ (s.continuous i) (s.compact i) _
    (ConicalMomentWeights.radial_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb

theorem tangentCorrection_continuous (s : System p a) : Continuous (tangentCorrection s) := by
  apply continuous_finset_sum
  intro i _
  obtain ⟨C,hC,hb⟩ := ConicalMomentWeights.tangent_bound _ _ _ p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
  exact PolarMomentContinuity.moment_continuous _ (s.continuous i) (s.compact i) _
    (ConicalMomentWeights.tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb

theorem correction_moment_norm_le (s : System p a) (R M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i x, x ∈ closedBall (0 : Space) R → ‖s.correction i x‖ ≤ M)
    (i : Fin 3) (σ : Sphere → ℂ) (C : ℝ) (hσ : ∀ n, ‖σ n‖ ≤ C)
    (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ R) :
    ‖moment (s.correction i) σ r‖ ≤ M*C*(angularMeasure univ).toReal := by
  apply PolarMomentContinuity.moment_norm_le (s.correction i) σ M C hM hσ r
  intro n
  apply hb i
  simpa only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,
    AngularPower.sphere_norm,mul_one] using hrR

end OQ14.ConicalProjectionData

#print axioms OQ14.ConicalProjectionData.correction_memLp
#print axioms OQ14.ConicalProjectionData.correctionL2_ae
#print axioms OQ14.ConicalProjectionData.totalCoordinate_ae
#print axioms OQ14.ConicalProjectionData.actual_gauss_pairing
#print axioms OQ14.ConicalProjectionData.radialCorrection_continuous
#print axioms OQ14.ConicalProjectionData.tangentCorrection_continuous
#print axioms OQ14.ConicalProjectionData.correction_moment_norm_le
