import ConicalGraphApproximation
import RadialNormTest

/-! Literal annular cap-profile tests and their actual spatial weak gradients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ConicalAnnularTests
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalCapField OQ14.SphereCapH1
  OQ14.ConicalCutoffGradient OQ14.ConicalAnnularSource OQ14.ConicalComplexLocalization
  OQ14.ConicalGraphApproximation OQ14.InteriorTestDensity OQ14.WeakGreen
open scoped Topology SchwartzMap

def radialWeight (ν : ℝ) (η : ℝ → ℂ) (r : ℝ) : ℂ := ((r^(-ν) : ℝ) : ℂ)*η r

theorem radialWeight_tsupport (ν : ℝ) (η : ℝ → ℂ) : tsupport (radialWeight ν η) ⊆ tsupport η :=
  tsupport_mul_subset_right

theorem radialWeight_smooth (ν : ℝ) (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (h0 : 0 ∉ tsupport η) : ContDiff ℝ (⊤ : ℕ∞) (radialWeight ν η) := by
  apply contDiff_iff_contDiffAt.mpr
  intro r
  by_cases hr : r=0
  · subst r
    have hz : η =ᶠ[𝓝 (0 : ℝ)] 0 := by
      filter_upwards [isClosed_tsupport η |>.isOpen_compl.mem_nhds h0] with s hs
      exact image_eq_zero_of_nmem_tsupport hs
    have he : radialWeight ν η =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℂ)) := by
      filter_upwards [hz] with s hs
      simp only [radialWeight,hs,Pi.zero_apply,mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp r (Real.contDiffAt_rpow_const_of_ne hr)).mul hη.contDiffAt

theorem radialWeight_hasDerivAt (ν : ℝ) (η : ℝ → ℂ) (r : ℝ) (hr : 0 < r)
    (hη : DifferentiableAt ℝ η r) :
    HasDerivAt (radialWeight ν η)
      (((r^(-ν) : ℝ) : ℂ)*deriv η r-(ν : ℂ)*((r^(-ν-1) : ℝ) : ℂ)*η r) r := by
  have hp := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt r
    (Real.hasDerivAt_rpow_const (Or.inl hr.ne') :
      HasDerivAt (fun s : ℝ => s^(-ν)) ((-ν)*r^(-ν-1)) r)
  convert hp.mul hη.hasDerivAt using 1
  simp only [radialWeight,Complex.ofRealCLM_apply,Complex.ofReal_mul,Complex.ofReal_neg,Function.comp_def]
  ring

def multiplier (ν : ℝ) (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (h0 : 0 ∉ tsupport η) : SmoothInterior (univ : Set Space) := by
  have hreg := RadialNormTest.radialNorm_smooth (radialWeight ν η)
    (radialWeight_smooth ν η hη h0) (fun h => h0 (radialWeight_tsupport ν η h))
  have hcmp := RadialNormTest.radialNorm_compact (radialWeight ν η) hc.mul_left
  exact ⟨⟨⟨_,hreg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1),hcmp⟩,subset_univ _⟩,hreg⟩

theorem multiplier_apply (ν : ℝ) (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (h0 : 0 ∉ tsupport η) (x : Space) :
    (multiplier ν η hη hc h0).function x=radialWeight ν η ‖x‖ := rfl

theorem multiplier_partial (ν : ℝ) (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (h0 : 0 ∉ tsupport η) (x : Space) (hx : x≠0) (i : Fin 3) :
    dcoord (multiplier ν η hη hc h0).function x i=
      (((‖x‖^(-ν) : ℝ) : ℂ)*deriv η ‖x‖-(ν : ℂ)*((‖x‖^(-ν-1) : ℝ) : ℂ)*η ‖x‖)*
        ((x i/‖x‖ : ℝ) : ℂ) :=
  GreenKernel.radial_composition_partial _ _ x hx
    (radialWeight_hasDerivAt ν η ‖x‖ (norm_pos_iff.mpr hx) (hη.differentiable (by simp) _)) i

def angularTest (a t : ℝ) (η : ℝ → ℂ) (x : Space) : ℂ :=
  η ‖x‖*(field a t (unit x) : ℂ)

def angularDerivative (a t : ℝ) (η : ℝ → ℂ) (x : Space) (i : Fin 3) : ℂ :=
  deriv η ‖x‖*(field a t (unit x) : ℂ)*((unit x : Space) i : ℂ)+
    η ‖x‖/(‖x‖ : ℂ)*(SphereCapH1.gradient a t (unit x) i : ℂ)

private theorem powers_cancel (ν r : ℝ) (hr : 0 < r) :
    ((r^(-ν) : ℝ) : ℂ)*((r^ν : ℝ) : ℂ)=1 := by
  rw [← Complex.ofReal_mul,← Real.rpow_add hr]
  simp

theorem multiplier_potential (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) (x : Space) :
    (multiplier ν η hη hc (fun h => (hs h).1.false)).function x*(cutPotential χ ν a t x : ℂ)=
      angularTest a t η x := by
  by_cases he : η ‖x‖=0
  · simp only [multiplier_apply,radialWeight,he,mul_zero,zero_mul,angularTest]
  · have hx := hs (subset_tsupport η he)
    have hχ : χ x=1 := χ.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right] using hx.2.le)
    simp only [multiplier_apply,radialWeight,cutPotential,hχ,one_mul,potential,Complex.ofReal_mul,angularTest]
    calc
      _ = (((‖x‖^(-ν) : ℝ) : ℂ)*((‖x‖^ν : ℝ) : ℂ))*η ‖x‖*(field a t (unit x) : ℂ) := by ring
      _ = _ := by rw [powers_cancel ν ‖x‖ hx.1,one_mul]

theorem multiplier_tsupport (ν : ℝ) (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (h0 : 0 ∉ tsupport η) :
    tsupport (multiplier ν η hη hc h0).function ⊆ (norm : Space → ℝ) ⁻¹' tsupport η := by
  intro x hx
  exact radialWeight_tsupport ν η (RadialNormTest.radialNorm_tsupport (radialWeight ν η) hx)

theorem multiplier_gradient_polar (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (h0 : 0 ∉ tsupport η) (r : ℝ) (hr : 0 < r) (hR : r < χ.rIn)
    (n : AngularPower.Sphere) (i : Fin 3) :
    (multiplier ν η hη hc h0).function (r • (n : Space))*complexify (cutElectric χ ν a t) (r • (n : Space)) i+
      dcoord (multiplier ν η hη hc h0).function (r • (n : Space)) i*(cutPotential χ ν a t (r • (n : Space)) : ℂ)=
      angularDerivative a t η (r • (n : Space)) i := by
  have hn : ‖r • (n : Space)‖=r := by simp [norm_smul,AngularPower.sphere_norm,abs_of_pos hr]
  have hx : r • (n : Space)≠0 := by intro h; rw [h,norm_zero] at hn; linarith
  have hχ : χ (r • (n : Space))=1 := χ.one_of_mem_closedBall (by simpa only [mem_closedBall,dist_zero_right,hn] using hR.le)
  have hdχ := bump_fderiv_zero_inner χ (r • (n : Space)) (by simpa only [mem_ball,dist_zero_right,hn] using hR)
  have he : cutElectric χ ν a t (r • (n : Space))=electric ν a t (r • (n : Space)) := by
    ext j
    simp only [cutElectric,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,cutoffGradient_apply,hχ,hdχ,
      ContinuousLinearMap.zero_apply,mul_zero,add_zero,one_mul]
  have hu : cutPotential χ ν a t (r • (n : Space))=r^ν*field a t n := by
    rw [cutPotential,hχ,one_mul,potential_polar ν a t r hr n]
  have hpa : ((r^(ν-1) : ℝ) : ℂ)=((r^ν : ℝ) : ℂ)/(r : ℂ) := by
    rw [Real.rpow_sub hr,Real.rpow_one,Complex.ofReal_div]
  have hpb : ((r^(-ν-1) : ℝ) : ℂ)=((r^(-ν) : ℝ) : ℂ)/(r : ℂ) := by
    rw [Real.rpow_sub hr,Real.rpow_one,Complex.ofReal_div]
  dsimp only [complexify]
  rw [he,hu,multiplier_apply,multiplier_partial ν η hη hc h0 _ hx i]
  simp only [radialWeight,complexify,electric_polar ν a t r hr n,PiLp.smul_apply,smul_eq_mul,
    angularElectric,PiLp.add_apply,Complex.ofReal_mul,Complex.ofReal_add,hn,angularDerivative,
    unit_polar r hr n]
  have hcoord : (r*(n : Space) i/r : ℝ)=(n : Space) i := by field_simp [hr.ne']
  rw [hcoord,hpa,hpb]
  have hp := powers_cancel ν r hr
  field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
  linear_combination ((r : ℂ)*deriv η r*(field a t n : ℂ)*((n : Space) i : ℂ)+η r*(SphereCapH1.gradient a t n i : ℂ))*hp

theorem multiplier_gradient (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) (x : Space) (i : Fin 3) :
    (multiplier ν η hη hc (fun h => (hs h).1.false)).function x*complexify (cutElectric χ ν a t) x i+
      dcoord (multiplier ν η hη hc (fun h => (hs h).1.false)).function x i*(cutPotential χ ν a t x : ℂ)=
      angularDerivative a t η x i := by
  by_cases hsx : ‖x‖ ∈ tsupport η
  · have hp := (hs hsx).1
    have hx : x≠0 := norm_pos_iff.mp hp
    have hrep : ‖x‖ • (unit x : Space)=x := by
      simp only [unit,if_neg hx,smul_smul,mul_inv_cancel₀ hp.ne',one_smul]
    simpa only [hrep] using multiplier_gradient_polar χ ν a t η hη hc (fun h => (hs h).1.false)
      ‖x‖ hp (hs hsx).2 (unit x) i
  · have hm : x ∉ tsupport (multiplier ν η hη hc (fun h => (hs h).1.false)).function :=
      fun h => hsx (multiplier_tsupport ν η hη hc _ h)
    have hz := image_eq_zero_of_nmem_tsupport hm
    have hd := fderiv_of_not_mem_tsupport ℝ hm
    have hη0 := image_eq_zero_of_nmem_tsupport hsx
    have hηD : deriv η ‖x‖=0 := by
      by_contra hne
      exact hsx (support_deriv_subset hne)
    simp only [hz,dcoord,hd,ContinuousLinearMap.zero_apply,zero_mul,add_zero,
      angularDerivative,hηD,hη0,zero_div,zero_add]

def testL2 (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 ≤ ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) : WeakCurl.L2Scalar :=
  scaleL2 (multiplier ν η hη hc (fun h => (hs h).1.false)).function
    (multiplier ν η hη hc (fun h => (hs h).1.false)).regular.continuous
    (multiplier ν η hη hc (fun h => (hs h).1.false)).compact
    (potentialL2 χ ν a t hν ha ht ht1)

def gradientL2 (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 ≤ ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) (i : Fin 3) : WeakCurl.L2Scalar :=
  multipliedDerivative (multiplier ν η hη hc (fun h => (hs h).1.false))
    (potentialL2 χ ν a t hν ha ht ht1) (electricL2 χ ν a t hν ha ht ht1) i

theorem testL2_ae (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 ≤ ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) :
    (testL2 χ ν a t hν ha ht ht1 η hη hc hs : Space → ℂ) =ᵐ[volume] angularTest a t η := by
  let κ := multiplier ν η hη hc (fun h => (hs h).1.false)
  filter_upwards [scaleL2_ae κ.function κ.regular.continuous κ.compact
    (potentialL2 χ ν a t hν ha ht ht1),potentialL2_ae χ ν a t hν ha ht ht1] with x hv hu
  change scaleL2 κ.function κ.regular.continuous κ.compact (potentialL2 χ ν a t hν ha ht ht1) x=_
  rw [hv,hu]
  exact multiplier_potential χ ν a t η hη hc hs x

theorem gradientL2_ae (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 ≤ ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) (i : Fin 3) :
    (gradientL2 χ ν a t hν ha ht ht1 η hη hc hs i : Space → ℂ) =ᵐ[volume]
      fun x => angularDerivative a t η x i := by
  let κ := multiplier ν η hη hc (fun h => (hs h).1.false)
  filter_upwards [multipliedDerivative_ae κ (potentialL2 χ ν a t hν ha ht ht1)
    (electricL2 χ ν a t hν ha ht ht1) i,potentialL2_ae χ ν a t hν ha ht ht1,
    electricL2_ae χ ν a t hν ha ht ht1 i] with x hd hu he
  change multipliedDerivative κ (potentialL2 χ ν a t hν ha ht ht1)
    (electricL2 χ ν a t hν ha ht ht1) i x=_
  rw [hd,hu,he]
  exact multiplier_gradient χ ν a t η hη hc hs x i

theorem angularTest_memLp (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 ≤ ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) : MemLp (angularTest a t η) 2 (volume : Measure Space) :=
  MemLp.ae_eq (testL2_ae χ ν a t hν ha ht ht1 η hη hc hs) (Lp.memLp _)

theorem angularDerivative_memLp (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 ≤ ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) (i : Fin 3) :
    MemLp (fun x => angularDerivative a t η x i) 2 (volume : Measure Space) :=
  MemLp.ae_eq (gradientL2_ae χ ν a t hν ha ht ht1 η hη hc hs i) (Lp.memLp _)

theorem test_hasWeakPartial (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 < ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) (i : Fin 3) :
    DivCurlCompact.HasWeakPartial (testL2 χ ν a t hν.le ha ht ht1 η hη hc hs)
      (gradientL2 χ ν a t hν.le ha ht ht1 η hη hc hs i) i :=
  localized_hasWeakPartial _ (potential_compact χ ν a t hν.le ha ht ht1)
    (potential_hasWeakPartial χ ν a t hν ha ht ht1) i

theorem angular_graph_approximation (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 < ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) :
    ∃ f : ℕ → 𝓢(Space, ℂ),
      (∀ n, tsupport (f n : Space → ℂ) ⊆ (norm : Space → ℝ) ⁻¹' tsupport η) ∧
      Tendsto (fun n => FourierL2.embed (f n)) atTop
        (𝓝 (testL2 χ ν a t hν.le ha ht ht1 η hη hc hs)) ∧
      ∀ i, Tendsto (fun n => FourierL2.embed (GradientProjection.pderivative i (f n))) atTop
        (𝓝 (gradientL2 χ ν a t hν.le ha ht ht1 η hη hc hs i)) := by
  obtain ⟨f,hf,hv,hd⟩ := localized_graph_approximation (multiplier ν η hη hc (fun h => (hs h).1.false))
    (potential_compact χ ν a t hν.le ha ht ht1) (potential_hasWeakPartial χ ν a t hν ha ht ht1)
  exact ⟨f,fun n => (hf n).trans (multiplier_tsupport ν η hη hc _),hv,hd⟩

theorem divergence_angular_test (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (hν : 0 < ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (η : ℝ → ℂ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo (0 : ℝ) χ.rIn) (D : Fin 3 → WeakCurl.L2Scalar)
    (hweak : ∀ f : 𝓢(Space, ℂ), tsupport (f : Space → ℂ) ⊆ (norm : Space → ℝ) ⁻¹' tsupport η →
      (∑ i : Fin 3, ∫ x : Space, D i x*dcoord f x i)=0) :
    (∑ i : Fin 3, ∫ x : Space, D i x*angularDerivative a t η x i)=0 := by
  obtain ⟨f,hf,_,hd⟩ := angular_graph_approximation χ ν a t hν ha ht ht1 η hη hc hs
  have hl := (((scalarProduct (D 0)).continuous.tendsto _ |>.comp (hd 0)).add
    ((scalarProduct (D 1)).continuous.tendsto _ |>.comp (hd 1))).add
    ((scalarProduct (D 2)).continuous.tendsto _ |>.comp (hd 2))
  have hz (n : ℕ) :
      scalarProduct (D 0) (FourierL2.embed (GradientProjection.pderivative 0 (f n)))+
      scalarProduct (D 1) (FourierL2.embed (GradientProjection.pderivative 1 (f n)))+
      scalarProduct (D 2) (FourierL2.embed (GradientProjection.pderivative 2 (f n)))=0 := by
    simpa only [PartialSmoothing.scalarProduct_embed,GradientProjection.pderivative_apply,Fin.sum_univ_three]
      using hweak (f n) (hf n)
  have he := tendsto_nhds_unique hl
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun n => (hz n).symm)))
  have hp (i : Fin 3) : scalarProduct (D i) (gradientL2 χ ν a t hν.le ha ht ht1 η hη hc hs i)=
      ∫ x : Space, D i x*angularDerivative a t η x i := by
    rw [scalarProduct_integral]
    apply integral_congr_ae
    filter_upwards [gradientL2_ae χ ν a t hν.le ha ht ht1 η hη hc hs i] with x hx
    rw [hx]
  simpa only [Fin.sum_univ_three,hp] using he

end OQ14.ConicalAnnularTests

#print axioms OQ14.ConicalAnnularTests.radialWeight_tsupport
#print axioms OQ14.ConicalAnnularTests.radialWeight_smooth
#print axioms OQ14.ConicalAnnularTests.radialWeight_hasDerivAt
#print axioms OQ14.ConicalAnnularTests.multiplier_apply
#print axioms OQ14.ConicalAnnularTests.multiplier_partial
#print axioms OQ14.ConicalAnnularTests.multiplier_potential
#print axioms OQ14.ConicalAnnularTests.multiplier_tsupport
#print axioms OQ14.ConicalAnnularTests.multiplier_gradient_polar
#print axioms OQ14.ConicalAnnularTests.multiplier_gradient
#print axioms OQ14.ConicalAnnularTests.testL2_ae
#print axioms OQ14.ConicalAnnularTests.gradientL2_ae
#print axioms OQ14.ConicalAnnularTests.angularTest_memLp
#print axioms OQ14.ConicalAnnularTests.angularDerivative_memLp
#print axioms OQ14.ConicalAnnularTests.test_hasWeakPartial
#print axioms OQ14.ConicalAnnularTests.angular_graph_approximation
#print axioms OQ14.ConicalAnnularTests.divergence_angular_test
