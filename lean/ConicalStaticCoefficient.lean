import ConicalCoefficientIdentity

/-! Actual static annular pairing equals positive angular energy times radial normalization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalStaticCoefficient
open MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.ConicalStaticVolume
  OQ14.ConicalAnnularCoefficient OQ14.ConicalCoefficientIdentity OQ14.ConicalTangentialDivergence
  OQ14.ConicalCapField OQ14.ConicalCutoffGradient OQ14.ConicalComplexLocalization OQ14.ConicalAnnularSource
  OQ14.WeakGreen OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space

theorem static_pairing (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) :
    fieldPair p ζ hζ hc (ConicalStaticVolume.electric p)=
      (ConicalAngularEnergy.energy p.eigenvalue p.contrast p.threshold : ℂ)*radialFactor p ζ := by
  let f : Fin 3 → Space → ℂ := fun i x => (tangentField ζ p.eigenvalue p.contrast p.threshold x i : ℂ)*
    (cutElectric p.cutoff p.exponent p.eigenvalue p.threshold x i : ℂ)
  have hfi (i : Fin 3) : Integrable (f i) := by
    apply (scalarProduct_integrable (testCoordinate p ζ hζ hc i) (physicalCoordinate (ConicalStaticVolume.electric p) i)).congr
    filter_upwards [tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i,
      electric_ae p i] with x ht he
    exact congrArg₂ (fun a b : ℂ => a*b) ht he
  have he : fieldPair p ζ hζ hc (ConicalStaticVolume.electric p)=∫ x : Space, ∑ i : Fin 3, f i x := by
    rw [fieldPair_apply,integral_finset_sum _ (fun i _ => hfi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarProduct_integral]
    apply integral_congr_ae
    filter_upwards [tangentFieldL2_ae _ _ _ p.eigenvalue_bounds p.contrast_nonnegative p.threshold_pos p.threshold_lt_one ζ hζ hc i,
      electric_ae p i] with x ht he
    exact congrArg₂ (fun a b : ℂ => a*b) ht he
  rw [he,ComplexPolarIntegration.integral_polar_complex _ (integrable_finset_sum _ (fun i _ => hfi i))]
  have hinner (r : ℝ) (hr : 0 < r) : (∫ n : Sphere, ∑ i : Fin 3, f i (r • (n : Space)) ∂angularMeasure)=
      (ζ r : ℂ)*((r^(p.exponent-1) : ℝ) : ℂ)*(ConicalAngularEnergy.energy p.eigenvalue p.contrast p.threshold : ℂ) := by
    have hpoint (n : Sphere) : (∑ i : Fin 3, f i (r • (n : Space)))=
        ((ζ r*r^(p.exponent-1) : ℝ) : ℂ)*
          (CapSturmLiouville.coefficient p.contrast p.threshold ((n : Space) 2)*‖SphereCapH1.gradient p.eigenvalue p.threshold n‖^2 : ℝ) := by
      by_cases hz : ζ r=0
      · simp only [f,tangentField,norm_smul,sphere_norm,Real.norm_eq_abs,abs_of_pos hr,mul_one,hz,
          zero_mul,Complex.ofReal_zero,Finset.sum_const_zero]
      · have hri : r < p.cutoff.rIn := (hs (subset_tsupport ζ hz)).2
        have hx : r • (n : Space) ∈ ball (0 : Space) p.cutoff.rIn := by
          simpa only [mem_ball,dist_zero_right,norm_smul,sphere_norm,Real.norm_eq_abs,abs_of_pos hr,mul_one] using hri
        have hcut : cutElectric p.cutoff p.exponent p.eigenvalue p.threshold (r • (n : Space))=
            ConicalCapField.electric p.exponent p.eigenvalue p.threshold (r • (n : Space)) := by
          ext i
          simp only [cutElectric,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,cutoffGradient_apply,
            p.cutoff.one_of_mem_closedBall (ball_subset_closedBall hx),bump_fderiv_zero_inner p.cutoff _ hx,
            ContinuousLinearMap.zero_apply,one_mul,mul_zero,add_zero]
        simp only [f,hcut,ConicalCapField.electric_polar _ _ _ _ hr,PiLp.smul_apply,smul_eq_mul,
          tangentField,weightedTangent,PiLp.smul_apply,permittivity,unit_polar _ hr,norm_smul,sphere_norm,
          Real.norm_eq_abs,abs_of_pos hr,mul_one]
        simp only [← Complex.ofReal_mul]
        rw [← Complex.ofReal_sum]
        apply congrArg Complex.ofReal
        have hid := ConicalAngularEnergy.angular_tangent_identity p.exponent p.eigenvalue p.contrast p.threshold n
        calc
          _ = ζ r*r^(p.exponent-1)*(∑ i : Fin 3, angularElectric p.exponent p.eigenvalue p.threshold n i*
              (CapSturmLiouville.coefficient p.contrast p.threshold ((n : Space) 2)*SphereCapH1.gradient p.eigenvalue p.threshold n i)) := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = _ := by rw [hid]
    simp_rw [hpoint]
    rw [integral_const_mul]
    have hJ := Complex.ofRealCLM.integral_comp_comm
      (ConicalAngularEnergy.energy_integrable p.eigenvalue p.contrast p.threshold p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one)
    simpa only [Complex.ofRealCLM_apply,ConicalAngularEnergy.energy,Complex.ofReal_mul,mul_assoc] using congrArg
      (fun z : ℂ => (ζ r : ℂ)*((r^(p.exponent-1) : ℝ) : ℂ)*z) hJ
  rw [radialFactor,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  change (r^2 : ℂ)*(∫ n : Sphere, ∑ i : Fin 3, f i (r • (n : Space)) ∂angularMeasure)=
    (ConicalAngularEnergy.energy p.eigenvalue p.contrast p.threshold : ℂ)*
      ((r : ℂ)*(ζ r : ℂ)*ConicalRadialParticular.power p.exponent r)
  rw [hinner r hr]
  have hp : r*r^(p.exponent-1)=r^p.exponent := by
    conv_lhs => lhs; rw [← Real.rpow_one r]
    rw [← Real.rpow_add hr]
    congr 1
    ring
  have hpC := congrArg Complex.ofReal hp
  push_cast at hpC
  dsimp only [ConicalRadialParticular.power]
  linear_combination (r : ℂ)*(ζ r : ℂ)*(ConicalAngularEnergy.energy p.eigenvalue p.contrast p.threshold : ℂ)*hpC

theorem radialFactor_re_positive (p : Data) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) (hn : ∀ r, 0 ≤ ζ r)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hz₀ : ζ r₀≠0) : 0 < (radialFactor p ζ).re := by
  let g : ℝ → ℝ := fun r => r*ζ r*r^p.exponent
  have hg : Continuous g := (continuous_id.mul hζ.continuous).mul (Real.continuous_rpow_const p.exponent_pos.le)
  have hgc : HasCompactSupport g := (hc.mul_left).mul_right
  have hzero (r : ℝ) (hr : r ∉ Ioi (0 : ℝ)) : ζ r=0 :=
    image_eq_zero_of_nmem_tsupport (fun h => hr (hs h).1)
  have hgn : ∀ r, 0 ≤ g r := by
    intro r
    by_cases hr : 0 < r
    · exact mul_nonneg (mul_nonneg hr.le (hn r)) (Real.rpow_nonneg hr.le _)
    · simp only [g,hzero r hr,mul_zero,zero_mul,le_refl]
  have hgp : g r₀≠0 := mul_ne_zero (mul_ne_zero hr₀.ne' hz₀) (Real.rpow_pos_of_pos hr₀ _).ne'
  have hpos := hg.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hgc hgn hgp
  have hres : (∫ r in Ioi (0 : ℝ),g r)=∫ r,g r :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by simp only [g,hzero r hr,mul_zero,zero_mul])
  have hcast : radialFactor p ζ=((∫ r in Ioi (0 : ℝ),g r : ℝ) : ℂ) := by
    symm
    have hh := Complex.ofRealCLM.integral_comp_comm ((hg.integrable_of_hasCompactSupport (μ := volume) hgc).integrableOn (s := Ioi (0 : ℝ)))
    simpa only [Complex.ofRealCLM_apply,g,Complex.ofReal_mul,radialFactor,ConicalRadialParticular.power] using hh.symm
  rw [hcast,Complex.ofReal_re,hres]
  exact hpos

theorem static_pairing_ne_zero (p : Data) (hν : p.exponent < 1) (ζ : ℝ → ℝ)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) p.cutoff.rIn) (hn : ∀ r, 0 ≤ ζ r)
    (r₀ : ℝ) (hr₀ : 0 < r₀) (hz₀ : ζ r₀≠0) :
    fieldPair p ζ hζ hc (ConicalStaticVolume.electric p)≠0 := by
  rw [static_pairing p ζ hζ hc hs]
  have ha : p.eigenvalue ∈ Ioo (0 : ℝ) 2 := by
    refine ⟨ConicalProjectedDerivative.eigenvalue_pos p,?_⟩
    rw [← p.separation]
    nlinarith [mul_pos (sub_pos.mpr hν) (show 0 < p.exponent+2 by linarith [p.exponent_pos])]
  have hJ := ConicalAngularEnergy.energy_positive p.eigenvalue p.contrast p.threshold ha
    p.contrast_nonnegative p.threshold_pos p.threshold_lt_one
  apply mul_ne_zero (Complex.ofReal_ne_zero.mpr hJ.ne')
  intro hz
  have hr := radialFactor_re_positive p ζ hζ hc hs hn r₀ hr₀ hz₀
  simp only [hz,Complex.zero_re,lt_self_iff_false] at hr

end OQ14.ConicalStaticCoefficient


#print axioms OQ14.ConicalStaticCoefficient.static_pairing
#print axioms OQ14.ConicalStaticCoefficient.radialFactor_re_positive
#print axioms OQ14.ConicalStaticCoefficient.static_pairing_ne_zero
