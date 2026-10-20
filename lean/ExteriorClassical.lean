import ExteriorSmooth

/-! # Classical Maxwell equations for the actual exterior integral fields -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace OQ14.ExteriorClassical

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel OQ14.KernelConvolution Filter
open scoped Topology

theorem partial_smooth {f : Space → ℂ} {x : Space}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (j : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => dcoord f y j) x := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem partial_comm_at {f : Space → ℂ} {x : Space}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (i j : Fin 3) :
    dcoord (fun y => dcoord f y j) x i =
      dcoord (fun y => dcoord f y i) x j := by
  have hd := (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiableAt (by simp)
  simp only [dcoord, fderiv_clm_apply hd (differentiableAt_const _),
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.map_zero, ContinuousLinearMap.flip_apply, zero_add]
  exact (hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).isSymmSndFDerivAt
    (by simp) (basis i) (basis j)

theorem divergence_smooth (A : Field) {x : Space}
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (divergence A) x :=
  ((partial_smooth (hA 0) 0).add (partial_smooth (hA 1) 1)).add
    (partial_smooth (hA 2) 2)

theorem curl_smooth (A : Field) {x : Space}
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x) :
    ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => curl A y j) x := by
  intro j
  fin_cases j
  · exact (partial_smooth (hA 2) 1).sub (partial_smooth (hA 1) 2)
  · exact (partial_smooth (hA 0) 2).sub (partial_smooth (hA 2) 0)
  · exact (partial_smooth (hA 1) 0).sub (partial_smooth (hA 0) 1)

theorem curl_gradient_at {f : Space → ℂ} {x : Space}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) : curl (gradient f) x = 0 := by
  ext j
  fin_cases j <;> simp [curl, gradient, pd, partial_comm_at hf 1 2,
    partial_comm_at hf 2 0, partial_comm_at hf 0 1]

theorem partial_divergence (A : Field) {x : Space}
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x) (i : Fin 3) :
    dcoord (divergence A) x i =
      dcoord (fun y => pd A y 0 0) x i +
      dcoord (fun y => pd A y 1 1) x i +
      dcoord (fun y => pd A y 2 2) x i := by
  have hd (j : Fin 3) := (partial_smooth (hA j) j).differentiableAt (by simp)
  exact (partial_add ((hd 0).add (hd 1)) (hd 2) i).trans
    (by rw [partial_add (hd 0) (hd 1)]; rfl)

theorem curl_curl_at (A : Field) {x : Space}
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x) (i : Fin 3) :
    curl (curl A) x i = dcoord (divergence A) x i -
      divergence (gradient (fun y => A y i)) x := by
  have hd (j l : Fin 3) := (partial_smooth (hA j) l).differentiableAt (by simp)
  rw [partial_divergence A hA i]
  fin_cases i <;> dsimp [curl, pd, divergence, gradient] <;>
    simp only [partial_sub (hd _ _) (hd _ _)] <;>
    simp only [partial_comm_at (hA 0) 0 1, partial_comm_at (hA 0) 0 2,
      partial_comm_at (hA 1) 0 1, partial_comm_at (hA 1) 1 2,
      partial_comm_at (hA 2) 0 2, partial_comm_at (hA 2) 1 2] <;> ring

def electricPotential (k : ℝ) (A : Field) : Field :=
  fun x i => (k : ℂ)^2 * A x i + dcoord (divergence A) x i

def magneticPotential (k : ℝ) (A : Field) : Field :=
  fun x i => -(Complex.I * (k : ℂ)) * curl A x i

theorem potential_maxwell (k : ℝ) (A : Field) (x : Space)
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x)
    (hHelm : ∀ j, divergence (gradient (fun y => A y j)) x +
      (k : ℂ)^2 * A x j = 0) :
    MaxwellAt k 1 1 (electricPotential k A) (magneticPotential k A) x := by
  have hdA (j : Fin 3) := (hA j).differentiableAt (by simp)
  have hdG (j : Fin 3) := (partial_smooth (divergence_smooth A hA) j).differentiableAt (by simp)
  have hdC (j : Fin 3) := (curl_smooth A hA j).differentiableAt (by simp)
  constructor
  · change curl (fun y j => (k : ℂ)^2 * A y j + gradient (divergence A) y j) x = _
    rw [curl_add (fun y j => (k : ℂ)^2 * A y j) (gradient (divergence A))
      x (fun j => (hdA j).const_mul ((k : ℂ)^2)) hdG,
      curl_const_mul A x _ hdA, curl_gradient_at (divergence_smooth A hA)]
    ext j
    simp only [magneticPotential, Pi.zero_apply, add_zero, Complex.ofReal_one, mul_one]
    ring_nf
    simp [Complex.I_sq]
  · change curl (fun y j => -(Complex.I * (k : ℂ)) * curl A y j) x = _
    rw [curl_const_mul (curl A) x _ hdC]
    ext j
    rw [curl_curl_at A hA j]
    simp only [electricPotential, Complex.ofReal_one, mul_one]
    linear_combination Complex.I * (k : ℂ) * hHelm j

def potential (k : ℝ) (ρ : Fin 3 → Space → ℂ) : Field :=
  fun x j => response (phi k) (ρ j) x

theorem potential_smooth (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => potential k ρ y j) x :=
  fun j => ExteriorSmooth.scalar_response_contDiffAt k (ρ j) (hρ j) R (hc j) x hx

theorem dyadic_response (k : ℝ) (i j : Fin 3) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (R : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    response (fun z => DyadicKernel.dyadic k z i j) ρ x =
      (if i = j then (k : ℂ)^2 * response (phi k) ρ x else 0) +
      response (fun z => phiHessian k z i j) ρ x := by
  have hp := NewtonExteriorResponse.source_integrand_integrable (phi k) ρ
    (fun z hz => (phi_contDiffAt k z hz).continuousAt) hρ R hc x hx
  have hh := NewtonExteriorResponse.source_integrand_integrable
    (fun z => phiHessian k z i j) ρ (NewtonExterior.hessian_continuousAt k i j) hρ R hc x hx
  unfold response DyadicKernel.dyadic
  by_cases hij : i = j
  · simp only [hij, ite_true, mul_one]
    have he : (fun y => ρ y * ((k : ℂ)^2 * phi k (x-y) + phiHessian k (x-y) i j)) =
        (fun y => (k : ℂ)^2 * (ρ y * phi k (x-y)) + ρ y * phiHessian k (x-y) i j) := by
      funext y; ring
    simp only [hij] at he
    simp only [hij] at hh
    rw [he, integral_add (hp.const_mul ((k : ℂ)^2)) hh, integral_const_mul]
  · simp only [hij, ite_false, mul_zero, zero_add]

theorem electric_eq_potential (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    ExteriorContinuity.electric k ρ x = electricPotential k (potential k ρ) x := by
  have hs := potential_smooth k ρ hρ R hc x hx
  ext i
  unfold ExteriorContinuity.electric electricPotential
  rw [partial_divergence _ hs]
  simp only [potential, pd,
    ScalarExteriorSecond.response_second_partial k R _ _ _ (hρ _) (hc _) x hx]
  simp only [dyadic_response k _ _ _ (hρ _) R (hc _) x hx, Finset.sum_add_distrib]
  simp [Fin.sum_univ_succ]
  fin_cases i <;> simp <;> ring

theorem magnetic_eq_potential (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    MagneticResponse.magnetic k ρ x = magneticPotential k (potential k ρ) x := by
  ext i
  fin_cases i <;>
    simp [MagneticResponse.magnetic, magneticPotential, curl, pd, potential,
      WeakCurl.next, WeakCurl.previous,
      ScalarExterior.response_partial k R _ (hρ _) (hc _) x hx]

theorem curl_congr_nhds {E H : Field} {x : Space} (he : E =ᶠ[𝓝 x] H) :
    curl E x = curl H x := by
  have hp (i j : Fin 3) : pd E x i j = pd H x i j := by
    have he' : (fun y => E y j) =ᶠ[𝓝 x] (fun y => H y j) :=
      he.mono (fun _ hy => congrFun hy j)
    exact congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) he'.fderiv_eq
  ext i
  fin_cases i <;> simp only [curl, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, hp]

theorem exterior_maxwell (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    MaxwellAt k 1 1 (ExteriorContinuity.electric k ρ) (MagneticResponse.magnetic k ρ) x := by
  have hn : {z : Space | R < ‖z‖} ∈ 𝓝 x :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hx
  have he : ExteriorContinuity.electric k ρ =ᶠ[𝓝 x] electricPotential k (potential k ρ) := by
    filter_upwards [hn] with z hz
    exact electric_eq_potential k ρ hρ R hc z hz
  have hh : MagneticResponse.magnetic k ρ =ᶠ[𝓝 x] magneticPotential k (potential k ρ) := by
    filter_upwards [hn] with z hz
    exact magnetic_eq_potential k ρ hρ R hc z hz
  have hm := potential_maxwell k (potential k ρ) x (potential_smooth k ρ hρ R hc x hx)
    (fun j => ScalarExteriorSecond.response_helmholtz k R (ρ j) (hρ j) (hc j) x hx)
  unfold MaxwellAt at *
  rw [curl_congr_nhds he, curl_congr_nhds hh, he.eq_of_nhds, hh.eq_of_nhds]
  exact hm

theorem divergence_curl_at (A : Field) {x : Space}
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x) :
    divergence (curl A) x = 0 := by
  have hd (j l : Fin 3) := (partial_smooth (hA j) l).differentiableAt (by simp)
  dsimp [divergence, curl, pd]
  rw [partial_sub (hd 2 1) (hd 1 2), partial_sub (hd 0 2) (hd 2 0),
    partial_sub (hd 1 0) (hd 0 1)]
  rw [partial_comm_at (hA 2) 0 1, partial_comm_at (hA 1) 0 2,
    partial_comm_at (hA 0) 1 2]
  ring

theorem divergence_congr_nhds {E H : Field} {x : Space} (he : E =ᶠ[𝓝 x] H) :
    divergence E x = divergence H x := by
  have hp (i j : Fin 3) : pd E x i j = pd H x i j := by
    have he' : (fun y => E y j) =ᶠ[𝓝 x] (fun y => H y j) :=
      he.mono (fun _ hy => congrFun hy j)
    exact congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) he'.fderiv_eq
  simp only [divergence, hp]

theorem divergence_const_mul_at (A : Field) {x : Space} (c : ℂ)
    (hA : ∀ j, DifferentiableAt ℝ (fun y => A y j) x) :
    divergence (fun y j => c * A y j) x = c * divergence A x := by
  simp only [divergence, pd, partial_const_mul (hA _)]
  ring

theorem exterior_gauss (k : ℝ) (hk : k ≠ 0) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    divergence (ExteriorContinuity.electric k ρ) x = 0 ∧
      divergence (MagneticResponse.magnetic k ρ) x = 0 := by
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
  have hde := divergence_congr_nhds he
  have hdh := divergence_congr_nhds hh
  rw [divergence_curl_at _ hE, divergence_const_mul_at _ _
    (fun j => (hH j).differentiableAt (by simp))] at hde
  rw [divergence_curl_at _ hH, divergence_const_mul_at _ _
    (fun j => (hE j).differentiableAt (by simp))] at hdh
  have hkC : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  exact ⟨(mul_eq_zero.mp hdh.symm).resolve_left
      (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hkC),
    (mul_eq_zero.mp hde.symm).resolve_left (mul_ne_zero Complex.I_ne_zero hkC)⟩

end OQ14.ExteriorClassical

#print axioms OQ14.ExteriorClassical.partial_smooth
#print axioms OQ14.ExteriorClassical.partial_comm_at
#print axioms OQ14.ExteriorClassical.divergence_smooth
#print axioms OQ14.ExteriorClassical.curl_smooth
#print axioms OQ14.ExteriorClassical.curl_gradient_at
#print axioms OQ14.ExteriorClassical.partial_divergence
#print axioms OQ14.ExteriorClassical.curl_curl_at
#print axioms OQ14.ExteriorClassical.potential_maxwell
#print axioms OQ14.ExteriorClassical.potential_smooth
#print axioms OQ14.ExteriorClassical.dyadic_response
#print axioms OQ14.ExteriorClassical.electric_eq_potential
#print axioms OQ14.ExteriorClassical.magnetic_eq_potential
#print axioms OQ14.ExteriorClassical.curl_congr_nhds
#print axioms OQ14.ExteriorClassical.exterior_maxwell
#print axioms OQ14.ExteriorClassical.divergence_curl_at
#print axioms OQ14.ExteriorClassical.divergence_congr_nhds
#print axioms OQ14.ExteriorClassical.divergence_const_mul_at
#print axioms OQ14.ExteriorClassical.exterior_gauss
