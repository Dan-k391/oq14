import ConicalMomentWeights
import ConicalGradientGraph

/-! Actual conical moment identities for every genuine global L2 weak-gradient graph. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalGraphMoments
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalGradientGraph
  OQ14.ConicalRadialDivergence OQ14.ConicalTangentialDivergence OQ14.PolarMomentTesting
open scoped Topology
abbrev Space := Maxwell.Space

def valueMoment (p : Data) (g : Graph) (r : ℝ) : ℂ :=
  moment (g.value) (ConicalMomentWeights.scalar p.eigenvalue p.contrast p.threshold) r

def radialMoment (p : Data) (g : Graph) (r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (g.gradient i) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i) r

def tangentMoment (p : Data) (g : Graph) (r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (g.gradient i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r

def radialTest (ζ : ℝ → ℝ) (r : ℝ) : ℂ := ((r*ζ r : ℝ) : ℂ)

def divergenceTest (ζ : ℝ → ℝ) (r : ℝ) : ℂ := ((3*ζ r+r*deriv ζ r : ℝ) : ℂ)

private theorem radialTest_regular (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) : Continuous (radialTest ζ) :=
  Complex.continuous_ofReal.comp (continuous_id.mul hζ.continuous)

private theorem radialTest_compact (ζ : ℝ → ℝ) (hc : HasCompactSupport ζ) : HasCompactSupport (radialTest ζ) :=
  (hc.mul_left (f := fun r : ℝ => r)).comp_left (g := Complex.ofReal) (by simp)

private theorem divergenceTest_regular (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) : Continuous (divergenceTest ζ) :=
  Complex.continuous_ofReal.comp ((continuous_const.mul hζ.continuous).add
    (continuous_id.mul (hζ.continuous_deriv (by simp))))

private theorem divergenceTest_compact (ζ : ℝ → ℝ) (hc : HasCompactSupport ζ) : HasCompactSupport (divergenceTest ζ) :=
  ((hc.mul_left (f := fun _ => (3 : ℝ))).add (hc.deriv.mul_left (f := fun r => r))).comp_left (g := Complex.ofReal) (by simp)

theorem radial_field_identity (p : Data) (ζ : ℝ → ℝ) (x : Space) (i : Fin 3) :
    (radialField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)=
      ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*radialTest ζ ‖x‖ := by
  have h := ConicalMomentWeights.radial_product p.eigenvalue p.contrast p.threshold i x
  dsimp only [radialField,radialTest]
  push_cast at h ⊢
  linear_combination -(ζ ‖x‖ : ℂ)*h

theorem radial_divergence_identity (p : Data) (ζ : ℝ → ℝ) (x : Space) :
    (radialDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ)=
      ConicalMomentWeights.scalar p.eigenvalue p.contrast p.threshold (ConicalCapField.unit x)*divergenceTest ζ ‖x‖ := by
  rw [ConicalMomentWeights.scalar_unit]
  simp only [radialDivergence,divergenceTest,Complex.ofReal_mul]

theorem radial_moment_weak (p : Data) (g : Graph) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*radialTest ζ r*radialMoment p g r)+
      (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*divergenceTest ζ r*valueMoment p g r)=0 := by
  have h := radial_gradient_pairing p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc h0
    (g.value) (g.gradient) (g.weak)
  have hr (i : Fin 3) : (∫ x : Space, g.gradient i x*(radialField ζ p.eigenvalue p.contrast p.threshold x i : ℂ))=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*radialTest ζ r*
        moment (g.gradient i) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i) r := by
    obtain ⟨C,_,hC⟩ := ConicalMomentWeights.radial_bound p.eigenvalue p.contrast p.threshold
      p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    rw [show (fun x : Space => g.gradient i x*(radialField ζ p.eigenvalue p.contrast p.threshold x i : ℂ))=
        fun x => g.gradient i x*ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*radialTest ζ ‖x‖ by
      funext x; rw [radial_field_identity]; ring]
    exact integral_weighted_moment _ (Lp.memLp _) _
      (ConicalMomentWeights.radial_measurable p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i)
      C hC _ (radialTest_regular ζ hζ) (radialTest_compact ζ hc)
  have hu : (∫ x : Space, g.value x*(radialDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ))=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*divergenceTest ζ r*valueMoment p g r := by
    obtain ⟨C,_,hC⟩ := ConicalMomentWeights.scalar_bound p.eigenvalue p.contrast p.threshold
      p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one
    rw [show (fun x : Space => g.value x*(radialDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ))=
        fun x => g.value x*ConicalMomentWeights.scalar p.eigenvalue p.contrast p.threshold (ConicalCapField.unit x)*divergenceTest ζ ‖x‖ by
      funext x; rw [radial_divergence_identity]; ring]
    exact integral_weighted_moment _ (Lp.memLp _) _
      (ConicalMomentWeights.scalar_measurable p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one)
      C hC _ (divergenceTest_regular ζ hζ) (divergenceTest_compact ζ hc)
  have hi (i : Fin 3) : IntegrableOn (fun r : ℝ => (r^2 : ℂ)*radialTest ζ r*
      moment (g.gradient i) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i) r) (Ioi 0) := by
    obtain ⟨C,_,hC⟩ := ConicalMomentWeights.radial_bound p.eigenvalue p.contrast p.threshold
      p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integrable_weighted_moment _ (Lp.memLp _) _
      (ConicalMomentWeights.radial_measurable p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i)
      C hC _ (radialTest_regular ζ hζ) (radialTest_compact ζ hc)
  have hs : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*radialTest ζ r*radialMoment p g r)=
      ∑ i : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*radialTest ζ r*
        moment (g.gradient i) (ConicalMomentWeights.radial p.eigenvalue p.contrast p.threshold i) r := by
    simp only [radialMoment,Finset.mul_sum]
    exact integral_finset_sum _ (fun i _ => hi i)
  rw [hs]
  simpa only [hr,hu] using h

def tangentDivTest (a : ℝ) (ζ : ℝ → ℝ) (r : ℝ) : ℂ :=
  -(a : ℂ)*ConicalAnnularTests.radialWeight 1 (fun s => (ζ s : ℂ)) r

private theorem cast_support (ζ : ℝ → ℝ) : tsupport (fun r => (ζ r : ℂ))=tsupport ζ := by
  have he : Function.support (fun r => (ζ r : ℂ))=Function.support ζ := by
    ext r
    exact not_congr Complex.ofReal_eq_zero
  exact congrArg closure he

private theorem tangentDivTest_regular (a : ℝ) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (h0 : 0 ∉ tsupport ζ) : Continuous (tangentDivTest a ζ) := by
  have h0c : 0 ∉ tsupport (fun r => (ζ r : ℂ)) := by rwa [cast_support]
  exact continuous_const.mul (ConicalAnnularTests.radialWeight_smooth 1 _
    (Complex.ofRealCLM.contDiff.comp hζ) h0c).continuous

private theorem tangentDivTest_compact (a : ℝ) (ζ : ℝ → ℝ) (hc : HasCompactSupport ζ) :
    HasCompactSupport (tangentDivTest a ζ) :=
  ((hc.comp_left (g := Complex.ofReal) (by simp)).mul_left).mul_left

theorem tangent_field_identity (p : Data) (ζ : ℝ → ℝ) (x : Space) (i : Fin 3) :
    (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)=
      ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*(ζ ‖x‖ : ℂ) := by
  rw [ConicalMomentWeights.tangent_unit]
  simp only [tangentField,Complex.ofReal_mul]
  ring

theorem tangent_divergence_identity (p : Data) (ζ : ℝ → ℝ) (x : Space) :
    (tangentDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ)=
      ConicalMomentWeights.scalar p.eigenvalue p.contrast p.threshold (ConicalCapField.unit x)*tangentDivTest p.eigenvalue ζ ‖x‖ := by
  rw [ConicalMomentWeights.scalar_unit]
  simp only [tangentDivergence,tangentDivTest,ConicalAnnularTests.radialWeight,neg_mul,neg_one_mul,
    Real.rpow_neg_one,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

theorem tangent_moment_weak (p : Data) (g : Graph) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*tangentMoment p g r)+
      (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*tangentDivTest p.eigenvalue ζ r*valueMoment p g r)=0 := by
  have h := tangent_gradient_pairing p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one p.angular_root ζ hζ hc h0
    (g.value) (g.gradient) (g.weak)
  have hr (i : Fin 3) : (∫ x : Space, g.gradient i x*(tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ))=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*
        moment (g.gradient i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r := by
    obtain ⟨C,_,hC⟩ := ConicalMomentWeights.tangent_bound p.eigenvalue p.contrast p.threshold
      p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    rw [show (fun x : Space => g.gradient i x*(tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ))=
        fun x => g.gradient i x*ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i (ConicalCapField.unit x)*(ζ ‖x‖ : ℂ) by
      funext x; rw [tangent_field_identity]; ring]
    exact integral_weighted_moment _ (Lp.memLp _) _
      (ConicalMomentWeights.tangent_measurable p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i)
      C hC _ (Complex.continuous_ofReal.comp hζ.continuous) (hc.comp_left (g := Complex.ofReal) (by simp))
  have hu : (∫ x : Space, g.value x*(tangentDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ))=
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*tangentDivTest p.eigenvalue ζ r*valueMoment p g r := by
    obtain ⟨C,_,hC⟩ := ConicalMomentWeights.scalar_bound p.eigenvalue p.contrast p.threshold
      p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one
    rw [show (fun x : Space => g.value x*(tangentDivergence ζ p.eigenvalue p.contrast p.threshold x : ℂ))=
        fun x => g.value x*ConicalMomentWeights.scalar p.eigenvalue p.contrast p.threshold (ConicalCapField.unit x)*tangentDivTest p.eigenvalue ζ ‖x‖ by
      funext x; rw [tangent_divergence_identity]; ring]
    exact integral_weighted_moment _ (Lp.memLp _) _
      (ConicalMomentWeights.scalar_measurable p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one)
      C hC _ (tangentDivTest_regular p.eigenvalue ζ hζ h0) (tangentDivTest_compact p.eigenvalue ζ hc)
  have hi (i : Fin 3) : IntegrableOn (fun r : ℝ => (r^2 : ℂ)*(ζ r : ℂ)*
      moment (g.gradient i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r) (Ioi 0) := by
    obtain ⟨C,_,hC⟩ := ConicalMomentWeights.tangent_bound p.eigenvalue p.contrast p.threshold
      p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one i
    exact integrable_weighted_moment _ (Lp.memLp _) _
      (ConicalMomentWeights.tangent_measurable p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one i)
      C hC _ (Complex.continuous_ofReal.comp hζ.continuous) (hc.comp_left (g := Complex.ofReal) (by simp))
  have hs : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*tangentMoment p g r)=
      ∑ i : Fin 3, ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*
        moment (g.gradient i) (ConicalMomentWeights.tangent p.eigenvalue p.contrast p.threshold i) r := by
    simp only [tangentMoment,Finset.mul_sum]
    exact integral_finset_sum _ (fun i _ => hi i)
  rw [hs]
  simpa only [hr,hu] using h

theorem tangent_moment_weak_normalized (p : Data) (g : Graph) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*tangentMoment p g r)-
      (p.eigenvalue : ℂ)*(∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*valueMoment p g r)=0 := by
  have h := tangent_moment_weak p g ζ hζ hc h0
  have he : (∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*tangentDivTest p.eigenvalue ζ r*valueMoment p g r)=
      -(p.eigenvalue : ℂ)*(∫ r in Ioi (0 : ℝ), (r : ℂ)*(ζ r : ℂ)*valueMoment p g r) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only [tangentDivTest,ConicalAnnularTests.radialWeight]
    rw [show -(1 : ℝ)= -1 by ring,Real.rpow_neg_one,Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr (show r≠0 from (show 0 < r from hr).ne')]
    ring
  rw [he] at h
  simpa only [sub_eq_add_neg,mul_neg,neg_mul] using h

end OQ14.ConicalGraphMoments

#print axioms OQ14.ConicalGraphMoments.radial_field_identity
#print axioms OQ14.ConicalGraphMoments.radial_divergence_identity
#print axioms OQ14.ConicalGraphMoments.radial_moment_weak
#print axioms OQ14.ConicalGraphMoments.tangent_field_identity
#print axioms OQ14.ConicalGraphMoments.tangent_divergence_identity
#print axioms OQ14.ConicalGraphMoments.tangent_moment_weak
#print axioms OQ14.ConicalGraphMoments.tangent_moment_weak_normalized
