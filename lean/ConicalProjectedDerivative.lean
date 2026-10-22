import ConicalMomentIdentities

/-! Genuine radial weak derivative of the actual gradient-defined conical moment. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalProjectedDerivative
open MeasureTheory Set Filter OQ14.ConicalStaticVolume OQ14.ConicalMomentIdentities
open scoped Topology

def projected (p : Data) (k r : ℝ) : ℂ := (r : ℂ)/(p.eigenvalue : ℂ)*tangentMoment p k r

theorem eigenvalue_pos (p : Data) : 0 < p.eigenvalue := by
  rw [← p.separation]
  exact mul_pos p.exponent_pos (by linarith [p.exponent_pos])

def eliminationTest (a : ℝ) (ζ : ℝ → ℝ) (r : ℝ) : ℝ := r*(3*ζ r+r*deriv ζ r)/a

private theorem eliminationTest_smooth (a : ℝ) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) :
    ContDiff ℝ (⊤ : ℕ∞) (eliminationTest a ζ) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv ζ) := (contDiff_infty_iff_deriv.mp hζ).2
  exact (contDiff_id.mul ((contDiff_const.mul hζ).add (contDiff_id.mul hd))).div_const a

private theorem eliminationTest_compact (a : ℝ) (ζ : ℝ → ℝ) (hc : HasCompactSupport ζ) :
    HasCompactSupport (eliminationTest a ζ) := by
  have hB : HasCompactSupport (fun r : ℝ => 3*ζ r+r*deriv ζ r) :=
    (hc.mul_left (f := fun _ => (3 : ℝ))).add (hc.deriv.mul_left (f := fun r => r))
  have hR : HasCompactSupport (fun r : ℝ => r*(3*ζ r+r*deriv ζ r)) := hB.mul_left
  simpa only [eliminationTest,div_eq_mul_inv] using hR.mul_right (f' := fun _ => a⁻¹)

private theorem eliminationTest_support (a : ℝ) (ζ : ℝ → ℝ) : tsupport (eliminationTest a ζ) ⊆ tsupport ζ := by
  apply closure_minimal _ (isClosed_tsupport ζ)
  intro r hr
  by_contra hn
  have hζ := image_eq_zero_of_nmem_tsupport hn
  have hd : deriv ζ r=0 := by
    by_contra h
    exact hn (support_deriv_subset h)
  exact hr (by simp only [eliminationTest,hζ,hd,mul_zero,add_zero,zero_div])

theorem projected_weighted_weak (p : Data) (k : ℝ) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*radialTest ζ r*radialMoment p k r)+
      (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*divergenceTest ζ r*projected p k r)=0 := by
  have hR := radial_moment_weak p k ζ hζ hc h0
  have hT := tangent_moment_weak_normalized p k (eliminationTest p.eigenvalue ζ)
    (eliminationTest_smooth _ _ hζ) (eliminationTest_compact _ _ hc)
    (fun h => h0 (eliminationTest_support _ _ h))
  have hU : (p.eigenvalue : ℂ)*(∫ r in Ioi (0 : ℝ),
      (r : ℂ)*(eliminationTest p.eigenvalue ζ r : ℂ)*valueMoment p k r)=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*divergenceTest ζ r*valueMoment p k r := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [eliminationTest,divergenceTest]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (eigenvalue_pos p).ne']
    left
    ring
  have hP : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(eliminationTest p.eigenvalue ζ r : ℂ)*tangentMoment p k r)=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*divergenceTest ζ r*projected p k r := by
    apply integral_congr_ae
    filter_upwards with r
    dsimp only [eliminationTest,divergenceTest,projected]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (eigenvalue_pos p).ne']
    ring
  rw [hU,hP] at hT
  linear_combination hR+hT

def inverseCube (η : ℝ → ℝ) (r : ℝ) : ℝ := η r/r^3

theorem inverseCube_support (η : ℝ → ℝ) : tsupport (inverseCube η) ⊆ tsupport η := by
  apply closure_mono
  intro r hr
  intro hz
  exact hr (by simp only [inverseCube,hz,zero_div])

theorem inverseCube_smooth (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (h0 : 0 ∉ tsupport η) : ContDiff ℝ (⊤ : ℕ∞) (inverseCube η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r=0
  · subst r
    have hz : η =ᶠ[𝓝 (0 : ℝ)] 0 := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds h0] with s hs
      exact image_eq_zero_of_nmem_tsupport hs
    have he : inverseCube η =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [hz] with s hs
      simp only [inverseCube,hs,Pi.zero_apply,zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact hη.contDiffAt.div (contDiffAt_id.pow 3) (pow_ne_zero 3 hr)

theorem inverseCube_compact (η : ℝ → ℝ) (hc : HasCompactSupport η) : HasCompactSupport (inverseCube η) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (inverseCube_support η)

theorem inverseCube_hasDerivAt (η : ℝ → ℝ) (r : ℝ) (hr : r≠0) (hη : DifferentiableAt ℝ η r) :
    HasDerivAt (inverseCube η) (deriv η r/r^3-3*η r/r^4) r := by
  convert hη.hasDerivAt.div ((hasDerivAt_id r).pow 3) (pow_ne_zero 3 hr) using 1
  norm_num only [Nat.cast_ofNat,Nat.reduceSub,one_mul]
  field_simp [hr]
  ring

theorem projected_weak_derivative (p : Data) (k : ℝ) (η : ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (h0 : 0 ∉ tsupport η) :
    (∫ r in Ioi (0 : ℝ), (η r : ℂ)*radialMoment p k r)+
      (∫ r in Ioi (0 : ℝ), ((deriv η r : ℝ) : ℂ)*projected p k r)=0 := by
  have h := projected_weighted_weak p k (inverseCube η) (inverseCube_smooth η hη h0)
    (inverseCube_compact η hc) (fun h => h0 (inverseCube_support η h))
  have hR : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*radialTest (inverseCube η) r*radialMoment p k r)=
      ∫ r in Ioi (0 : ℝ), (η r : ℂ)*radialMoment p k r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only [radialTest,inverseCube]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (show r≠0 from (show 0 < r from hr).ne')]
    ring
  have hU : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*divergenceTest (inverseCube η) r*projected p k r)=
      ∫ r in Ioi (0 : ℝ), ((deriv η r : ℝ) : ℂ)*projected p k r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hd := (inverseCube_hasDerivAt η r (show r≠0 from (show 0 < r from hr).ne')
      (hη.differentiable (by simp) r)).deriv
    dsimp only [divergenceTest]
    rw [hd]
    dsimp only [inverseCube]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (show r≠0 from (show 0 < r from hr).ne')]
    ring
  rwa [hR,hU] at h

end OQ14.ConicalProjectedDerivative

#print axioms OQ14.ConicalProjectedDerivative.eigenvalue_pos
#print axioms OQ14.ConicalProjectedDerivative.projected_weighted_weak
#print axioms OQ14.ConicalProjectedDerivative.inverseCube_support
#print axioms OQ14.ConicalProjectedDerivative.inverseCube_smooth
#print axioms OQ14.ConicalProjectedDerivative.inverseCube_compact
#print axioms OQ14.ConicalProjectedDerivative.inverseCube_hasDerivAt
#print axioms OQ14.ConicalProjectedDerivative.projected_weak_derivative
