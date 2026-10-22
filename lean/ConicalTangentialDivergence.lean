import ConicalRadialDivergence
import RealDivergenceComplex

/-! Actual tangential H(div) test identity from the proved spherical eigenproblem. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ConicalTangentialDivergence
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.ConicalCapField OQ14.ConicalRadialDivergence OQ14.ConicalAnnularSource
open scoped Topology

def weightedTangent (a d t : ℝ) (x : Space) : Space :=
  permittivity d t x • SphereCapH1.gradient a t (unit x)

theorem weightedTangent_measurable (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    Measurable (weightedTangent a d t) :=
  (permittivity_measurable d t).smul ((gradient_measurable a t ha ht ht1).comp unit_measurable)

theorem weightedTangent_bound (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) : ∃ C ≥ (0 : ℝ), ∀ x, ‖weightedTangent a d t x‖ ≤ C := by
  obtain ⟨C,hC,hb⟩ := angular_bounds 0 a t ha ht ht1
  refine ⟨(1+d)*C,by positivity,fun x => ?_⟩
  have hε := ConicalStaticField.permittivity_bounds d t hd x
  have hG : ‖SphereCapH1.gradient a t (unit x)‖ ≤ C := by
    simpa only [angularElectric,zero_mul,zero_smul,zero_add] using (hb (unit x)).2
  rw [weightedTangent,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ permittivity d t x)]
  exact mul_le_mul hε.2 hG (norm_nonneg _) (by positivity)

def tangentField (ζ : ℝ → ℝ) (a d t : ℝ) (x : Space) (i : Fin 3) : ℝ :=
  ζ ‖x‖*weightedTangent a d t x i

def tangentDivergence (ζ : ℝ → ℝ) (a d t : ℝ) (x : Space) : ℝ :=
  (-a)*(‖x‖⁻¹*ζ ‖x‖)*spatialWeight a d t x

theorem tangentField_memLp (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : Continuous ζ) (hc : HasCompactSupport ζ) (i : Fin 3) :
    MemLp (fun x => tangentField ζ a d t x i) 2 (volume : Measure Space) := by
  obtain ⟨C,_,hC⟩ := weightedTangent_bound a d t ha hd ht ht1
  have hm := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.measurable.comp
    (weightedTangent_measurable a d t ha ht ht1)
  apply ((hζ.comp continuous_norm).memLp_of_hasCompactSupport (radialReal_compact ζ hc)).of_le_mul (c := C)
    (((hζ.comp continuous_norm).measurable.mul hm).aestronglyMeasurable)
  filter_upwards with x
  change ‖ζ ‖x‖*weightedTangent a d t x i‖ ≤ C*‖ζ ‖x‖‖
  rw [norm_mul,mul_comm C]
  exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le _ i).trans (hC x)) (norm_nonneg _)

private theorem cast_support (ζ : ℝ → ℝ) : tsupport (fun r => (ζ r : ℂ))=tsupport ζ := by
  have he : Function.support (fun r => (ζ r : ℂ))=Function.support ζ := by
    ext r
    exact not_congr Complex.ofReal_eq_zero
  exact congrArg closure he

private theorem inverse_radial_regular (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    Continuous (fun x : Space => ‖x‖⁻¹*ζ ‖x‖) ∧ HasCompactSupport (fun x : Space => ‖x‖⁻¹*ζ ‖x‖) := by
  have hζc : ContDiff ℝ (⊤ : ℕ∞) (fun r => (ζ r : ℂ)) := Complex.ofRealCLM.contDiff.comp hζ
  have hcc : HasCompactSupport (fun r => (ζ r : ℂ)) := hc.comp_left (g := Complex.ofReal) (by simp)
  have h0c : 0 ∉ tsupport (fun r => (ζ r : ℂ)) := by rwa [cast_support]
  let κ := ConicalAnnularTests.multiplier 1 (fun r => (ζ r : ℂ)) hζc hcc h0c
  have he : (fun x : Space => ‖x‖⁻¹*ζ ‖x‖)=(fun x => (κ.function x).re) := by
    funext x
    simp only [κ,ConicalAnnularTests.multiplier_apply,ConicalAnnularTests.radialWeight,
      neg_mul,neg_one_mul,Real.rpow_neg_one,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
  rw [he]
  exact ⟨Complex.continuous_re.comp κ.regular.continuous,κ.compact.comp_left (g := Complex.re) rfl⟩

theorem tangentDivergence_memLp (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    MemLp (tangentDivergence ζ a d t) 2 (volume : Measure Space) := by
  obtain ⟨hq,hqc⟩ := inverse_radial_regular ζ hζ hc h0
  have h := (weight_mul_memLp a d t ha hd ht ht1 _ hq hqc).const_mul (-a)
  convert h using 1
  funext x
  dsimp only [tangentDivergence]
  ring

theorem tangentField_compact (ζ : ℝ → ℝ) (hc : HasCompactSupport ζ) (a d t : ℝ) (i : Fin 3) :
    HasCompactSupport (fun x : Space => tangentField ζ a d t x i) :=
  (radialReal_compact ζ hc).mul_right

theorem tangential_real_weak_divergence (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a=0)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hcζ : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, tangentDivergence ζ a d t x*ψ x)+
      (∑ i : Fin 3, ∫ x : Space, tangentField ζ a d t x i*fderiv ℝ ψ x (basis i))=0 := by
  have hi (i : Fin 3) : Integrable (fun x : Space => tangentField ζ a d t x i*fderiv ℝ ψ x (basis i)) := by
    simpa only [smul_eq_mul] using
      ((tangentField_memLp a d t ha hd ht ht1 ζ hζ.continuous hcζ i).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const) (hc.fderiv_apply ℝ (basis i))
  let L : Space → ℝ := fun x => ζ ‖x‖*permittivity d t x*fderiv ℝ ψ x (SphereCapH1.gradient a t (unit x))
  have he (x : Space) : (∑ i : Fin 3, tangentField ζ a d t x i*fderiv ℝ ψ x (basis i))=L x := by
    have hv : (∑ i : Fin 3, (SphereCapH1.gradient a t (unit x)) i • basis i)=SphereCapH1.gradient a t (unit x) := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (SphereCapH1.gradient a t (unit x))
    have hG : fderiv ℝ ψ x (SphereCapH1.gradient a t (unit x))=
        ∑ i : Fin 3, (SphereCapH1.gradient a t (unit x)) i*fderiv ℝ ψ x (basis i) := by
      conv_lhs => rw [← hv,map_sum]
      simp only [map_smul,smul_eq_mul]
    dsimp only [L]
    rw [hG,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [tangentField,weightedTangent,PiLp.smul_apply,smul_eq_mul]
    ring
  have hiL : Integrable L := by
    convert integrable_finset_sum Finset.univ (fun i _ => hi i) using 1
    funext x
    exact (he x).symm
  have hiD : Integrable (fun x : Space => tangentDivergence ζ a d t x*ψ x) := by
    simpa only [smul_eq_mul] using
      ((tangentDivergence_memLp a d t ha hd ht ht1 ζ hζ hcζ h0).locallyIntegrable (by norm_num)).integrable_smul_right_of_hasCompactSupport
        hψ.continuous hc
  have hs : (∑ i : Fin 3, ∫ x : Space, tangentField ζ a d t x i*fderiv ℝ ψ x (basis i))=∫ x : Space, L x := by
    rw [← integral_finset_sum _ (fun i _ => hi i)]
    apply integral_congr_ae
    filter_upwards with x
    exact he x
  rw [hs,PolarIntegration.integral_polar _ hiD,PolarIntegration.integral_polar _ hiL]
  have htrace (r : ℝ) (hr : 0 < r) :
      r^2*(∫ n : Sphere, L (r • (n : Space)) ∂angularMeasure)=
        -(r^2*(∫ n : Sphere, tangentDivergence ζ a d t (r • (n : Space))*ψ (r • (n : Space)) ∂angularMeasure)) := by
    have hn (n : Sphere) : ‖r • (n : Space)‖=r := by simp [norm_smul,sphere_norm,abs_of_pos hr]
    have hL : (∫ n : Sphere, L (r • (n : Space)) ∂angularMeasure)=ζ r*
        (∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*fderiv ℝ ψ (r • (n : Space)) (SphereCapH1.gradient a t n) ∂angularMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with n
      simp only [L,hn,permittivity_polar d t r hr n,unit_polar r hr n,mul_assoc]
    have hD : (∫ n : Sphere, tangentDivergence ζ a d t (r • (n : Space))*ψ (r • (n : Space)) ∂angularMeasure)=
        (-a)*(r⁻¹*ζ r)*(∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*(field a t n*ψ (r • (n : Space))) ∂angularMeasure) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with n
      simp only [tangentDivergence,spatialWeight,hn,permittivity_polar d t r hr n,unit_polar r hr n]
      ring
    rw [hL,hD]
    have h := ConicalAngularTests.scaled_weighted_weak a d t r ha ht ht1 hroot ψ hψ
    calc
      _ = r*ζ r*(r*(∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
          fderiv ℝ ψ (r • (n : Space)) (SphereCapH1.gradient a t n) ∂angularMeasure)) := by ring
      _ = r*ζ r*(a*(∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
          (field a t n*ψ (r • (n : Space))) ∂angularMeasure)) := by rw [h]
      _ = _ := by field_simp [hr.ne']; ring
  have hneg : (∫ r in Ioi (0 : ℝ), r^2*(∫ n : Sphere, L (r • (n : Space)) ∂angularMeasure))=
      -(∫ r in Ioi (0 : ℝ), r^2*(∫ n : Sphere, tangentDivergence ζ a d t (r • (n : Space))*ψ (r • (n : Space)) ∂angularMeasure)) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    exact htrace r hr
  rw [hneg]
  exact add_neg_cancel _

def tangentFieldL2 (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (i : Fin 3) : WeakCurl.L2Scalar :=
  ((tangentField_memLp a d t ha hd ht ht1 ζ hζ.continuous hc i).ofReal).toLp
    (fun x => (tangentField ζ a d t x i : ℂ))

def tangentDivergenceL2 (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) : WeakCurl.L2Scalar :=
  ((tangentDivergence_memLp a d t ha hd ht ht1 ζ hζ hc h0).ofReal).toLp
    (fun x => (tangentDivergence ζ a d t x : ℂ))

theorem tangent_hasWeakDivergence (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a=0)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    DivCurlCompact.HasWeakDivergence (tangentFieldL2 a d t ha hd ht ht1 ζ hζ hc)
      (tangentDivergenceL2 a d t ha hd ht ht1 ζ hζ hc h0) :=
  RealDivergenceComplex.of_real_tests _ _ (tangentField_memLp a d t ha hd ht ht1 ζ hζ.continuous hc)
    (tangentDivergence_memLp a d t ha hd ht ht1 ζ hζ hc h0)
    (tangential_real_weak_divergence a d t ha hd ht ht1 hroot ζ hζ hc h0)

theorem tangentFieldL2_ae (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (i : Fin 3) :
    (tangentFieldL2 a d t ha hd ht ht1 ζ hζ hc i : Space → ℂ) =ᵐ[volume]
      fun x => (tangentField ζ a d t x i : ℂ) :=
  ((tangentField_memLp a d t ha hd ht ht1 ζ hζ.continuous hc i).ofReal).coeFn_toLp

theorem tangentDivergenceL2_ae (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ) :
    (tangentDivergenceL2 a d t ha hd ht ht1 ζ hζ hc h0 : Space → ℂ) =ᵐ[volume]
      fun x => (tangentDivergence ζ a d t x : ℂ) :=
  ((tangentDivergence_memLp a d t ha hd ht ht1 ζ hζ hc h0).ofReal).coeFn_toLp

theorem tangentFieldL2_compact (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (i : Fin 3) : DivCurlCompact.CompactRepresentative (tangentFieldL2 a d t ha hd ht ht1 ζ hζ hc i) :=
  ⟨_,(tangentField_compact ζ hc a d t i).comp_left (g := Complex.ofReal) (by simp),
    tangentFieldL2_ae a d t ha hd ht ht1 ζ hζ hc i⟩

theorem tangent_gradient_pairing (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a=0)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) (h0 : 0 ∉ tsupport ζ)
    (u : WeakCurl.L2Scalar) (G : WeakCurl.L2Vector)
    (hG : ∀ i, DivCurlCompact.HasWeakPartial u (G i) i) :
    (∑ i : Fin 3, ∫ x : Space, G i x*(tangentField ζ a d t x i : ℂ))+
      (∫ x : Space, u x*(tangentDivergence ζ a d t x : ℂ))=0 := by
  have h := WeakDivergenceGraph.weak_gradient_divergence_integral u G
    (tangentFieldL2 a d t ha hd ht ht1 ζ hζ hc) (tangentDivergenceL2 a d t ha hd ht ht1 ζ hζ hc h0)
    hG (tangentFieldL2_compact a d t ha hd ht ht1 ζ hζ hc)
    (tangent_hasWeakDivergence a d t ha hd ht ht1 hroot ζ hζ hc h0)
  have hF (i : Fin 3) : (∫ x : Space, G i x*tangentFieldL2 a d t ha hd ht ht1 ζ hζ hc i x)=
      ∫ x : Space, G i x*(tangentField ζ a d t x i : ℂ) := by
    apply integral_congr_ae
    filter_upwards [tangentFieldL2_ae a d t ha hd ht ht1 ζ hζ hc i] with x hx
    rw [hx]
  have hD : (∫ x : Space, u x*tangentDivergenceL2 a d t ha hd ht ht1 ζ hζ hc h0 x)=
      ∫ x : Space, u x*(tangentDivergence ζ a d t x : ℂ) := by
    apply integral_congr_ae
    filter_upwards [tangentDivergenceL2_ae a d t ha hd ht ht1 ζ hζ hc h0] with x hx
    rw [hx]
  simpa only [hF,hD] using h

end OQ14.ConicalTangentialDivergence

#print axioms OQ14.ConicalTangentialDivergence.weightedTangent_measurable
#print axioms OQ14.ConicalTangentialDivergence.weightedTangent_bound
#print axioms OQ14.ConicalTangentialDivergence.tangentField_memLp
#print axioms OQ14.ConicalTangentialDivergence.tangentDivergence_memLp
#print axioms OQ14.ConicalTangentialDivergence.tangentField_compact
#print axioms OQ14.ConicalTangentialDivergence.tangential_real_weak_divergence
#print axioms OQ14.ConicalTangentialDivergence.tangent_hasWeakDivergence
#print axioms OQ14.ConicalTangentialDivergence.tangentFieldL2_ae
#print axioms OQ14.ConicalTangentialDivergence.tangentDivergenceL2_ae
#print axioms OQ14.ConicalTangentialDivergence.tangentFieldL2_compact
#print axioms OQ14.ConicalTangentialDivergence.tangent_gradient_pairing
