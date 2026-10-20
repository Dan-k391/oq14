import ExteriorClassical

/-!
The actual exterior electric and magnetic source fields satisfy scalar
Helmholtz equations componentwise. The Laplacian is the trace of the genuine
Euclidean second Frechet derivative, not an additional field relation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ExteriorHelmholtz
open MeasureTheory Metric Filter OQ14.Maxwell OQ14.ExteriorClassical
open scoped Topology

def laplacian (f : Space → ℂ) (x : Space) : ℂ :=
  ∑ i : Fin 3, dcoord (fun y => dcoord f y i) x i

theorem laplacian_eq_divergence_gradient (f : Space → ℂ) (x : Space) :
    laplacian f x = divergence (gradient f) x := by
  simp only [laplacian, Fin.sum_univ_three, divergence, gradient, pd]

theorem laplacian_eq_fderiv_trace (f : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    laplacian f x = ∑ i : Fin 3, fderiv ℝ (fderiv ℝ f) x (basis i) (basis i) := by
  have hd := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  unfold laplacian
  apply Finset.sum_congr rfl
  intro i _
  simp only [dcoord, fderiv_clm_apply hd (differentiableAt_const _),
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.map_zero, ContinuousLinearMap.flip_apply, zero_add]

theorem curl_curl_laplacian (A : Field) (x : Space)
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x) (i : Fin 3) :
    curl (curl A) x i = dcoord (divergence A) x i - laplacian (fun y => A y i) x := by
  rw [laplacian_eq_divergence_gradient]
  exact curl_curl_at A hA i

theorem partial_zero_of_eventually_zero (f : Space → ℂ) (x : Space)
    (hf : f =ᶠ[𝓝 x] 0) (i : Fin 3) : dcoord f x i = 0 := by
  unfold dcoord
  rw [hf.fderiv_eq]
  simp

theorem exterior_curl_curl (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    (∀ i, curl (curl (ExteriorContinuity.electric k ρ)) x i =
      (k : ℂ)^2 * ExteriorContinuity.electric k ρ x i) ∧
    (∀ i, curl (curl (MagneticResponse.magnetic k ρ)) x i =
      (k : ℂ)^2 * MagneticResponse.magnetic k ρ x i) := by
  have hE := contDiffAt_pi.mp (ExteriorSmooth.electric_contDiffAt k ρ hρ R hc x hx)
  have hH := contDiffAt_pi.mp (ExteriorSmooth.magnetic_contDiffAt k ρ hρ R hc x hx)
  have hn : {z : Space | R < ‖z‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have he : curl (ExteriorContinuity.electric k ρ) =ᶠ[𝓝 x]
      (fun z j => Complex.I * k * MagneticResponse.magnetic k ρ z j) := by
    filter_upwards [hn] with z hz
    simpa only [Complex.ofReal_one, mul_one] using (exterior_maxwell k ρ hρ R hc z hz).1
  have hh : curl (MagneticResponse.magnetic k ρ) =ᶠ[𝓝 x]
      (fun z j => -Complex.I * k * ExteriorContinuity.electric k ρ z j) := by
    filter_upwards [hn] with z hz
    simpa only [Complex.ofReal_one, mul_one] using (exterior_maxwell k ρ hρ R hc z hz).2
  have hec := curl_congr_nhds he
  have hhc := curl_congr_nhds hh
  rw [curl_const_mul _ _ _ (fun j => (hH j).differentiableAt (by simp)), hh.eq_of_nhds] at hec
  rw [curl_const_mul _ _ _ (fun j => (hE j).differentiableAt (by simp)), he.eq_of_nhds] at hhc
  constructor
  · intro i
    rw [hec]
    dsimp
    ring_nf
    simp [Complex.I_sq]
  · intro i
    rw [hhc]
    dsimp
    ring_nf
    simp [Complex.I_sq]

theorem exterior_helmholtz (k : ℝ) (hk : k ≠ 0) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    (∀ i, laplacian (fun y => ExteriorContinuity.electric k ρ y i) x +
      (k : ℂ)^2 * ExteriorContinuity.electric k ρ x i = 0) ∧
    (∀ i, laplacian (fun y => MagneticResponse.magnetic k ρ y i) x +
      (k : ℂ)^2 * MagneticResponse.magnetic k ρ x i = 0) := by
  have hE := contDiffAt_pi.mp (ExteriorSmooth.electric_contDiffAt k ρ hρ R hc x hx)
  have hH := contDiffAt_pi.mp (ExteriorSmooth.magnetic_contDiffAt k ρ hρ R hc x hx)
  have hn : {z : Space | R < ‖z‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have hde : divergence (ExteriorContinuity.electric k ρ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hn] with z hz
    exact (exterior_gauss k hk ρ hρ R hc z hz).1
  have hdh : divergence (MagneticResponse.magnetic k ρ) =ᶠ[𝓝 x] 0 := by
    filter_upwards [hn] with z hz
    exact (exterior_gauss k hk ρ hρ R hc z hz).2
  have hcc := exterior_curl_curl k ρ hρ R hc x hx
  constructor
  · intro i
    have hi := curl_curl_laplacian (ExteriorContinuity.electric k ρ) x hE i
    rw [hcc.1 i, partial_zero_of_eventually_zero _ x hde i, zero_sub] at hi
    linear_combination hi
  · intro i
    have hi := curl_curl_laplacian (MagneticResponse.magnetic k ρ) x hH i
    rw [hcc.2 i, partial_zero_of_eventually_zero _ x hdh i, zero_sub] at hi
    linear_combination hi

theorem electric_helmholtz (k : ℝ) (hk : k ≠ 0) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) (i : Fin 3) :
    laplacian (fun y => ExteriorContinuity.electric k ρ y i) x +
      (k : ℂ)^2 * ExteriorContinuity.electric k ρ x i = 0 :=
  (exterior_helmholtz k hk ρ hρ R hc x hx).1 i

theorem magnetic_helmholtz (k : ℝ) (hk : k ≠ 0) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) (i : Fin 3) :
    laplacian (fun y => MagneticResponse.magnetic k ρ y i) x +
      (k : ℂ)^2 * MagneticResponse.magnetic k ρ x i = 0 :=
  (exterior_helmholtz k hk ρ hρ R hc x hx).2 i

end OQ14.ExteriorHelmholtz

#print axioms OQ14.ExteriorHelmholtz.laplacian_eq_divergence_gradient
#print axioms OQ14.ExteriorHelmholtz.laplacian_eq_fderiv_trace
#print axioms OQ14.ExteriorHelmholtz.curl_curl_laplacian
#print axioms OQ14.ExteriorHelmholtz.partial_zero_of_eventually_zero
#print axioms OQ14.ExteriorHelmholtz.exterior_curl_curl
#print axioms OQ14.ExteriorHelmholtz.exterior_helmholtz
#print axioms OQ14.ExteriorHelmholtz.electric_helmholtz
#print axioms OQ14.ExteriorHelmholtz.magnetic_helmholtz
