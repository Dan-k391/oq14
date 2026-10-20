import MaxwellPlaneTail

/-! # Actual compact source kernels separated from the observation plane -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.PlaneSourceKernel

open MeasureTheory Metric Set OQ14.Maxwell OQ14.MaxwellPlaneTail
  OQ14.MaxwellRadiation OQ14.KernelConvolution OQ14.ScalarRadiation
open scoped Topology

abbrev Source := Fin 3 → Space → ℂ
abbrev Plane := PlaneInverseCube.Plane

structure Admissible (R d : ℝ) (ρ : Source) : Prop where
  integrable : ∀ j, Integrable (ρ j)
  support : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0
  gap : ∀ j y, ρ j y ≠ 0 → d ≤ |y 2|

def sourceRegion (R d : ℝ) : Set Space := closedBall 0 R ∩ {y | d ≤ |y 2|}

theorem sourceRegion_compact (R d : ℝ) : IsCompact (sourceRegion R d) :=
  (isCompact_closedBall (0 : Space) R).inter_right
    (isClosed_le continuous_const ((EuclideanSpace.proj 2).continuous.abs))

theorem gap_distance (d : ℝ) (q : Plane) (y : Space) (hy : d ≤ |y 2|) :
    d ≤ ‖planePoint q-y‖ := by
  have h := PiLp.norm_apply_le (planePoint q-y) 2
  have he : (planePoint q-y) 2 = -y 2 := by simp [planePoint]
  rw [he,Real.norm_eq_abs,abs_neg] at h
  exact hy.trans h

theorem scalar_kernel_bound (K : Space → ℝ)
    (hK : ∀ z, z ≠ 0 → ContinuousAt K z) (R d T : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : Plane, ‖q‖ ≤ T → ∀ y ∈ sourceRegion R d,
      K (planePoint q-y) ≤ C := by
  have hcomp := (isCompact_closedBall (0 : Plane) T).prod (sourceRegion_compact R d)
  have hcont : ContinuousOn (fun p : Plane × Space => K (planePoint p.1-p.2))
      (closedBall 0 T ×ˢ sourceRegion R d) := by
    intro p hp
    have hn : planePoint p.1-p.2 ≠ 0 := norm_pos_iff.mp
      (hd.trans_le (gap_distance d p.1 p.2 hp.2.2))
    exact ((hK _ hn).comp (f := fun p : Plane × Space => planePoint p.1-p.2)
      ((planePoint_continuous.comp continuous_fst).sub
      continuous_snd).continuousAt).continuousWithinAt
  obtain ⟨C,hC⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max C 1,lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right C 1),?_⟩
  intro q hq y hy
  have hh := hC (q,y) ⟨by simpa only [mem_closedBall,dist_zero_right] using hq,hy⟩
  exact (le_abs_self _).trans (hh.trans (le_max_left C 1))

def kernelSize (k : ℝ) (z : Space) : ℝ :=
  (∑ i : Fin 3, ∑ j : Fin 3, ‖DyadicKernel.dyadic k z i j‖)+
    ∑ i : Fin 3, ‖GreenKernel.phiGradient k z i‖

theorem kernelSize_continuousAt (k : ℝ) (z : Space) (hz : z ≠ 0) :
    ContinuousAt (kernelSize k) z := by
  apply ContinuousAt.add
  · exact tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _
      (fun j _ => (ExteriorContinuity.dyadic_continuousAt k i j z hz).norm))
  · exact tendsto_finset_sum _ (fun i _ =>
      (KernelGradient.gradient_differentiableAt k i z hz).continuousAt.norm)

theorem dyadic_le_kernelSize (k : ℝ) (z : Space) (i j : Fin 3) :
    ‖DyadicKernel.dyadic k z i j‖ ≤ kernelSize k z := by
  have hi : ‖DyadicKernel.dyadic k z i j‖ ≤ ∑ j : Fin 3, ‖DyadicKernel.dyadic k z i j‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have hj : (∑ j : Fin 3, ‖DyadicKernel.dyadic k z i j‖) ≤
      ∑ i : Fin 3, ∑ j : Fin 3, ‖DyadicKernel.dyadic k z i j‖ :=
    Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ i)
  exact (hi.trans hj).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))

theorem gradient_le_kernelSize (k : ℝ) (z : Space) (i : Fin 3) :
    ‖GreenKernel.phiGradient k z i‖ ≤ kernelSize k z := by
  exact (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ i)).trans
    (le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _))))

theorem actual_kernel_bound (k R d T : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : Plane, ‖q‖ ≤ T → ∀ y ∈ sourceRegion R d,
      (∀ i j : Fin 3, ‖DyadicKernel.dyadic k (planePoint q-y) i j‖ ≤ C) ∧
      (∀ i : Fin 3, ‖GreenKernel.phiGradient k (planePoint q-y) i‖ ≤ C) := by
  obtain ⟨C,hC,hbound⟩ := scalar_kernel_bound (kernelSize k) (kernelSize_continuousAt k) R d T hd
  exact ⟨C,hC,fun q hq y hy =>
    ⟨fun i j => (dyadic_le_kernelSize k _ i j).trans (hbound q hq y hy),
      fun i => (gradient_le_kernelSize k _ i).trans (hbound q hq y hy)⟩⟩

theorem source_mem_region (R d : ℝ) (ρ : Source) (hρ : Admissible R d ρ)
    (j : Fin 3) (y : Space) (hy : ρ j y ≠ 0) : y ∈ sourceRegion R d := by
  refine ⟨?_,hρ.gap j y hy⟩
  by_contra hn
  exact hy (hρ.support j y hn)

theorem dyadic_measurable (k : ℝ) (i j : Fin 3) :
    Measurable (fun z : Space => DyadicKernel.dyadic k z i j) := by
  unfold DyadicKernel.dyadic GreenKernel.phiHessian GreenKernel.phi
    GreenKernel.radial GreenKernel.radialD GreenKernel.radialDD
  fun_prop

theorem response_plane_continuous (K : Space → ℂ) (hKm : Measurable K)
    (hK : ∀ z, z ≠ 0 → ContinuousAt K z) (R d : ℝ) (hd : 0 < d)
    (ρ : Source) (hρ : Admissible R d ρ) (j : Fin 3) :
    Continuous (fun q : Plane => response K (ρ j) (planePoint q)) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  obtain ⟨C,hC,hbound⟩ := scalar_kernel_bound (fun z => ‖K z‖)
    (fun z hz => (hK z hz).norm) R d (‖a‖+1) hd
  have hball (q : Plane) (hq : q ∈ ball a 1) : ‖q‖ ≤ ‖a‖+1 := by
    have hdq : ‖q-a‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hq
    have hnorm := norm_add_le (q-a) a
    rw [sub_add_cancel] at hnorm
    linarith
  have hb (q : Plane) (hq : q ∈ ball a 1) (y : Space) (hy : ρ j y ≠ 0) :
      ‖K (planePoint q-y)‖ ≤ C := hbound q (hball q hq) y (source_mem_region R d ρ hρ j y hy)
  apply continuousAt_of_dominated (F := fun q y => ρ j y*K (planePoint q-y))
    (bound := fun y => C*‖ρ j y‖)
  · filter_upwards [ball_mem_nhds a (by norm_num : (0 : ℝ) < 1)] with q hq
    exact (source_integrand_integrable K (ρ j) hKm (hρ.integrable j) (planePoint q) C (hb q hq)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds a (by norm_num : (0 : ℝ) < 1)] with q hq
    filter_upwards with y
    by_cases hy : ρ j y = 0
    · simp [hy]
    · rw [norm_mul,mul_comm C]
      exact mul_le_mul_of_nonneg_left (hb q hq y hy) (norm_nonneg _)
  · exact (hρ.integrable j).norm.const_mul C
  · filter_upwards with y
    by_cases hy : ρ j y = 0
    · simp only [hy,zero_mul]
      exact continuousAt_const
    have hn : planePoint a-y ≠ 0 := norm_pos_iff.mp
      (hd.trans_le (gap_distance d a y (hρ.gap j y hy)))
    exact continuousAt_const.mul ((hK _ hn).comp (f := fun q : Plane => planePoint q-y)
      (planePoint_continuous.sub continuous_const).continuousAt)

theorem admissible_sub (R d : ℝ) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) : Admissible R d (ρ-σ) := by
  refine ⟨fun j => (hρ.integrable j).sub (hσ.integrable j),?_,?_⟩
  · intro j y hy
    simp only [Pi.sub_apply,hρ.support j y hy,hσ.support j y hy,sub_self]
  · intro j y hy
    by_cases h : ρ j y = 0
    · have hn : σ j y ≠ 0 := by intro hs; exact hy (by simp [h,hs])
      exact hσ.gap j y hn
    · exact hρ.gap j y h

theorem sourceMass_le_sub_add (ρ σ : Source)
    (hρ : ∀ j, Integrable (ρ j)) (hσ : ∀ j, Integrable (σ j)) :
    sourceMass ρ ≤ sourceMass (ρ-σ)+sourceMass σ := by
  have hj (j : Fin 3) : (∫ y, ‖ρ j y‖) ≤ (∫ y, ‖ρ j y-σ j y‖)+(∫ y, ‖σ j y‖) := by
    change (∫ y, ‖ρ j y‖) ≤ (∫ y, ‖(ρ j-σ j) y‖)+(∫ y, ‖σ j y‖)
    rw [← integral_add ((hρ j).sub (hσ j)).norm (hσ j).norm]
    apply integral_mono_ae (hρ j).norm (((hρ j).sub (hσ j)).norm.add (hσ j).norm)
    filter_upwards with y
    have hn := norm_add_le (ρ j y-σ j y) (σ j y)
    rwa [sub_add_cancel] at hn
  exact (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)).trans_eq
    (by simp only [sourceMass,Pi.sub_apply,Finset.sum_add_distrib])

theorem response_plane_integrable (K : Space → ℂ) (hKm : Measurable K)
    (hK : ∀ z, z ≠ 0 → ContinuousAt K z) (R d : ℝ) (hd : 0 < d)
    (ρ : Source) (hρ : Admissible R d ρ) (q : Plane) (j : Fin 3) :
    Integrable (fun y => ρ j y*K (planePoint q-y)) := by
  obtain ⟨C,_,hbound⟩ := scalar_kernel_bound (fun z => ‖K z‖)
    (fun z hz => (hK z hz).norm) R d ‖q‖ hd
  exact source_integrand_integrable K (ρ j) hKm (hρ.integrable j) (planePoint q) C
    (fun y hy => hbound q le_rfl y (source_mem_region R d ρ hρ j y hy))

theorem response_plane_sub (K : Space → ℂ) (hKm : Measurable K)
    (hK : ∀ z, z ≠ 0 → ContinuousAt K z) (R d : ℝ) (hd : 0 < d)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ) (q : Plane) (j : Fin 3) :
    response K ((ρ-σ) j) (planePoint q) =
      response K (ρ j) (planePoint q)-response K (σ j) (planePoint q) := by
  simp only [response,Pi.sub_apply,sub_mul]
  exact integral_sub (response_plane_integrable K hKm hK R d hd ρ hρ q j)
    (response_plane_integrable K hKm hK R d hd σ hσ q j)

theorem electric_plane_sub (k R d : ℝ) (hd : 0 < d) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) (q : Plane) :
    ExteriorContinuity.electric k (ρ-σ) (planePoint q) =
      ExteriorContinuity.electric k ρ (planePoint q)-ExteriorContinuity.electric k σ (planePoint q) := by
  funext i
  change (∑ j : Fin 3, response (fun z => DyadicKernel.dyadic k z i j) ((ρ-σ) j) (planePoint q)) = _
  rw [show (∑ j : Fin 3, response (fun z => DyadicKernel.dyadic k z i j) ((ρ-σ) j) (planePoint q)) =
      ∑ j : Fin 3, (response (fun z => DyadicKernel.dyadic k z i j) (ρ j) (planePoint q)-
        response (fun z => DyadicKernel.dyadic k z i j) (σ j) (planePoint q)) from
    Finset.sum_congr rfl (fun j _ => response_plane_sub _ (dyadic_measurable k i j)
      (fun z hz => ExteriorContinuity.dyadic_continuousAt k i j z hz) R d hd ρ σ hρ hσ q j)]
  exact Finset.sum_sub_distrib

theorem magnetic_plane_sub (k R d : ℝ) (hd : 0 < d) (ρ σ : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) (q : Plane) :
    MagneticResponse.magnetic k (ρ-σ) (planePoint q) =
      MagneticResponse.magnetic k ρ (planePoint q)-MagneticResponse.magnetic k σ (planePoint q) := by
  funext i
  change -(Complex.I*(k : ℂ)) *
    (response (fun z => GreenKernel.phiGradient k z (WeakCurl.next i)) ((ρ-σ) (WeakCurl.previous i)) (planePoint q)-
      response (fun z => GreenKernel.phiGradient k z (WeakCurl.previous i)) ((ρ-σ) (WeakCurl.next i)) (planePoint q)) = _
  rw [response_plane_sub _ (KernelGradient.gradient_measurable k _)
    (fun z hz => (KernelGradient.gradient_differentiableAt k _ z hz).continuousAt) R d hd ρ σ hρ hσ q,
    response_plane_sub _ (KernelGradient.gradient_measurable k _)
    (fun z hz => (KernelGradient.gradient_differentiableAt k _ z hz).continuousAt) R d hd ρ σ hρ hσ q]
  simp only [Pi.sub_apply,MagneticResponse.magnetic]
  ring

theorem bilinear_plane_sub (k R d : ℝ) (hd : 0 < d) (ρ σ ρ' σ' : Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (hρ' : Admissible R d ρ') (hσ' : Admissible R d σ') (q : Plane) :
    bilinearFlux k ρ σ (planePoint q)-bilinearFlux k ρ' σ' (planePoint q) =
      bilinearFlux k (ρ-ρ') σ (planePoint q)+bilinearFlux k ρ' (σ-σ') (planePoint q) := by
  unfold bilinearFlux
  rw [electric_plane_sub k R d hd ρ ρ' hρ hρ' q,magnetic_plane_sub k R d hd σ σ' hσ hσ' q]
  simp [cross_apply,conjugate]
  ring

theorem local_field_bounds (k R d T : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : Source, Admissible R d ρ → ∀ q : Plane, ‖q‖ ≤ T →
      (∀ i : Fin 3, ‖ExteriorContinuity.electric k ρ (planePoint q) i‖ ≤ C*sourceMass ρ) ∧
      (∀ i : Fin 3, ‖MagneticResponse.magnetic k ρ (planePoint q) i‖ ≤ 2 * |k| * C*sourceMass ρ) := by
  obtain ⟨C,hC,hbound⟩ := actual_kernel_bound k R d T hd
  refine ⟨C,hC,?_⟩
  intro ρ hρ q hq
  have he (i j : Fin 3) :
      ‖response (fun z => DyadicKernel.dyadic k z i j) (ρ j) (planePoint q)‖ ≤ C*(∫ y, ‖ρ j y‖) :=
    response_norm_bound _ _ (dyadic_measurable k i j) (hρ.integrable j) _ C
      (fun y hy => (hbound q hq y (source_mem_region R d ρ hρ j y hy)).1 i j)
  have hg (i j : Fin 3) :
      ‖response (fun z => GreenKernel.phiGradient k z i) (ρ j) (planePoint q)‖ ≤ C*sourceMass ρ :=
    (response_norm_bound _ _ (KernelGradient.gradient_measurable k i) (hρ.integrable j) _ C
      (fun y hy => (hbound q hq y (source_mem_region R d ρ hρ j y hy)).2 i)).trans
        (mul_le_mul_of_nonneg_left (component_mass_le ρ j) hC.le)
  constructor
  · intro i
    apply (norm_sum_le _ _).trans
    exact (Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => he i j)).trans_eq
      (by simp only [sourceMass,Finset.mul_sum])
  · intro i
    simp only [MagneticResponse.magnetic,norm_mul,norm_neg,Complex.norm_I,one_mul,
      Complex.norm_real,Real.norm_eq_abs]
    apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg k)).trans
    exact (mul_le_mul_of_nonneg_left (add_le_add (hg (WeakCurl.next i) (WeakCurl.previous i))
      (hg (WeakCurl.previous i) (WeakCurl.next i))) (abs_nonneg k)).trans_eq (by ring)

theorem electric_plane_continuous (k R d : ℝ) (hd : 0 < d)
    (ρ : Source) (hρ : Admissible R d ρ) (i : Fin 3) :
    Continuous (fun q : Plane => ExteriorContinuity.electric k ρ (planePoint q) i) := by
  exact continuous_finset_sum _ (fun j _ => response_plane_continuous _ (dyadic_measurable k i j)
    (fun z hz => ExteriorContinuity.dyadic_continuousAt k i j z hz) R d hd ρ hρ j)

theorem magnetic_plane_continuous (k R d : ℝ) (hd : 0 < d)
    (ρ : Source) (hρ : Admissible R d ρ) (i : Fin 3) :
    Continuous (fun q : Plane => MagneticResponse.magnetic k ρ (planePoint q) i) := by
  exact continuous_const.mul ((response_plane_continuous _ (KernelGradient.gradient_measurable k _)
    (fun z hz => (KernelGradient.gradient_differentiableAt k _ z hz).continuousAt)
      R d hd ρ hρ (WeakCurl.previous i)).sub
    (response_plane_continuous _ (KernelGradient.gradient_measurable k _)
    (fun z hz => (KernelGradient.gradient_differentiableAt k _ z hz).continuousAt)
      R d hd ρ hρ (WeakCurl.next i)))

theorem bilinear_plane_continuous (k R d : ℝ) (hd : 0 < d)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ) :
    Continuous (fun q : Plane => bilinearFlux k ρ σ (planePoint q)) := by
  exact ((electric_plane_continuous k R d hd ρ hρ 0).mul
    (magnetic_plane_continuous k R d hd σ hσ 1).star).sub
    ((electric_plane_continuous k R d hd ρ hρ 1).mul
      (magnetic_plane_continuous k R d hd σ hσ 0).star)

end OQ14.PlaneSourceKernel

#print axioms OQ14.PlaneSourceKernel.sourceRegion_compact
#print axioms OQ14.PlaneSourceKernel.gap_distance
#print axioms OQ14.PlaneSourceKernel.scalar_kernel_bound
#print axioms OQ14.PlaneSourceKernel.kernelSize_continuousAt
#print axioms OQ14.PlaneSourceKernel.dyadic_le_kernelSize
#print axioms OQ14.PlaneSourceKernel.gradient_le_kernelSize
#print axioms OQ14.PlaneSourceKernel.actual_kernel_bound
#print axioms OQ14.PlaneSourceKernel.source_mem_region
#print axioms OQ14.PlaneSourceKernel.dyadic_measurable
#print axioms OQ14.PlaneSourceKernel.response_plane_continuous
#print axioms OQ14.PlaneSourceKernel.admissible_sub
#print axioms OQ14.PlaneSourceKernel.sourceMass_le_sub_add
#print axioms OQ14.PlaneSourceKernel.response_plane_integrable
#print axioms OQ14.PlaneSourceKernel.response_plane_sub
#print axioms OQ14.PlaneSourceKernel.electric_plane_sub
#print axioms OQ14.PlaneSourceKernel.magnetic_plane_sub
#print axioms OQ14.PlaneSourceKernel.bilinear_plane_sub
#print axioms OQ14.PlaneSourceKernel.local_field_bounds
#print axioms OQ14.PlaneSourceKernel.electric_plane_continuous
#print axioms OQ14.PlaneSourceKernel.magnetic_plane_continuous
#print axioms OQ14.PlaneSourceKernel.bilinear_plane_continuous
