import ConicalAnnularCoefficient
import ConicalLocalExpansion

/-! Actual angular projection paired against a genuine annular L2 test. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalLocalCoefficient
open MeasureTheory Set Filter OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalAnnularCoefficient
  OQ14.ConicalTangentialDivergence OQ14.ConicalGradientGraph OQ14.PolarMomentTesting
  OQ14.ConicalProjectionData OQ14.ConicalMomentWeights OQ14.ConicalGraphMoments OQ14.ConicalGraphProjection OQ14.WeakGreen
open scoped Topology
abbrev Space := Maxwell.Space

def gradientPair {p : Data} {a : ℝ} (s : System p a) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) : ℂ :=
  ∑ i : Fin 3, WeakGreen.scalarProduct (testCoordinate p ζ hζ hc i) (s.graph.gradient i)

theorem projected_pairing {p : Data} {a : ℝ} (s : System p a) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    gradientPair s ζ hζ hc=(p.eigenvalue : ℂ)*
      ∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*projected p s.graph r := by
  have hi (i : Fin 3) : IntegrableOn (fun r : ℝ => (r^2 : ℂ)*(ζ r : ℂ)*
      moment (s.graph.gradient i) (tangent p.eigenvalue p.contrast p.threshold i) r) (Ioi (0 : ℝ)) := by
    obtain ⟨C,_,hb⟩ := tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integrable_weighted_moment _ (Lp.memLp _) _
      (tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _
      (Complex.continuous_ofReal.comp hζ.continuous) (hc.comp_left (g := Complex.ofReal) (by simp))
  have hp (i : Fin 3) : scalarProduct (testCoordinate p ζ hζ hc i) (s.graph.gradient i)=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*moment (s.graph.gradient i) (tangent p.eigenvalue p.contrast p.threshold i) r := by
    rw [scalarProduct_integral]
    have he : (∫ x : Space, testCoordinate p ζ hζ hc i x*s.graph.gradient i x)=
        ∫ x : Space, s.graph.gradient i x*tangent p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*(ζ ‖x‖ : ℂ) := by
      apply integral_congr_ae
      filter_upwards [tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i] with x hx
      change testCoordinate p ζ hζ hc i x*s.graph.gradient i x=_
      dsimp only [testCoordinate]
      rw [hx,ConicalGraphMoments.tangent_field_identity]
      ring
    rw [he]
    obtain ⟨C,_,hb⟩ := tangent_bound _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integral_weighted_moment _ (Lp.memLp _) _
      (tangent_measurable _ _ _ p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i) C hb _
      (Complex.continuous_ofReal.comp hζ.continuous) (hc.comp_left (g := Complex.ofReal) (by simp))
  rw [gradientPair]
  simp only [hp]
  rw [← integral_finset_sum _ (fun i _ => hi i),← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  simp only [← Finset.mul_sum,projected,tangentMoment]
  field_simp [Complex.ofReal_ne_zero.mpr (eigenvalue_pos p).ne']
  ring

def radialFactor (p : Data) (ζ : ℝ → ℝ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.power p.exponent r

def particularPair {p : Data} {a : ℝ} (s : System p a) (ζ : ℝ → ℝ) : ℂ := (p.eigenvalue : ℂ)*
  ∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.particular p.exponent
    (radialCorrection s) (tangentCorrection s) r

theorem coefficient_identity {p : Data} {a : ℝ} (s : System p a) (ha : 0 < a) (hai : a < p.cutoff.rIn) (hν : p.exponent < 1)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) a) :
    ∃ c : ℂ, (projected p s.graph =ᵐ[volume.restrict (Ioo (0 : ℝ) a)] fun r =>
      c*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
        (radialCorrection s) (tangentCorrection s) r) ∧
      gradientPair s ζ hζ hc=(p.eigenvalue : ℂ)*c*radialFactor p ζ+particularPair s ζ := by
  obtain ⟨c,he⟩ := ConicalLocalExpansion.actual_projected_expansion s ha hai hν
  have hcη : HasCompactSupport (fun r : ℝ => r*ζ r) := hc.mul_left
  have hη : Continuous (fun r : ℝ => r*ζ r) := continuous_id.mul hζ.continuous
  have hpow : Continuous (ConicalRadialParticular.power p.exponent) :=
    Complex.continuous_ofReal.comp (Real.continuous_rpow_const p.exponent_pos.le)
  have hiPow : IntegrableOn (fun r : ℝ => (r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.power p.exponent r) (Ioi (0 : ℝ)) := by
    have hi := ((Complex.continuous_ofReal.comp hη).mul hpow).integrable_of_hasCompactSupport (μ := volume)
      ((hcη.comp_left (g := Complex.ofReal) (by simp)).mul_right)
    simpa only [Function.comp_def,Complex.ofReal_mul] using hi.integrableOn (s := Ioi (0 : ℝ))
  have hpLoc := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((ConicalFiniteExpansion.particular_memLp p.exponent a ⟨p.exponent_pos,hν⟩
      (radialCorrection s) (tangentCorrection s)
      (radialCorrection_continuous s).continuousOn
      (tangentCorrection_continuous s).continuousOn).locallyIntegrable (by norm_num))
  have hiPart : IntegrableOn (fun r : ℝ => (r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.particular p.exponent
      (radialCorrection s) (tangentCorrection s) r) (Ioi (0 : ℝ)) := by
    have hi := SmoothLocalRepresentative.cutoff_integrable _ _ hpLoc (fun r => r*ζ r) hη hcη
      (tsupport_mul_subset_right.trans hs)
    simpa only [Complex.ofReal_mul] using hi.integrableOn
  have hfun : (∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*projected p s.graph r)=
      c*(∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.power p.exponent r)+
      ∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.particular p.exponent
        (radialCorrection s) (tangentCorrection s) r := by
    rw [← integral_const_mul,← integral_add (hiPow.const_mul c) hiPart]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (ae_imp_of_ae_restrict he)] with r hr
    by_cases hx : r ∈ Ioo (0 : ℝ) a
    · rw [hr hx]
      ring
    · have hz : ζ r=0 := image_eq_zero_of_nmem_tsupport (fun h => hx (hs h))
      simp only [hz,Complex.ofReal_zero,mul_zero,zero_mul,add_zero]
  refine ⟨c,he,?_⟩
  rw [projected_pairing,hfun]
  dsimp only [radialFactor,particularPair]
  ring

end OQ14.ConicalLocalCoefficient


#print axioms OQ14.ConicalLocalCoefficient.projected_pairing
#print axioms OQ14.ConicalLocalCoefficient.coefficient_identity
