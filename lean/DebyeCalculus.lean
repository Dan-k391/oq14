import HelmholtzTestCalculus

/-! Genuine local differential calculus for scalar-to-vector Debye waves.
The spatial reconstruction and source normalization require further results. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.DebyeCalculus
open OQ14.Maxwell OQ14.ExteriorClassical OQ14.ExteriorHelmholtz
  OQ14.HelmholtzTestCalculus OQ14.ModalDipole Filter
open scoped Topology

theorem partial_congr {f g : Space → ℂ} {x : Space}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 3) : dcoord f x i = dcoord g x i :=
  congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) h.fderiv_eq

theorem partial_comm_two {f : Space → ℂ} {x : Space}
    (hf : ContDiffAt ℝ 2 f x) (i j : Fin 3) :
    dcoord (fun y => dcoord f y j) x i = dcoord (fun y => dcoord f y i) x j := by
  have hd := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  simp only [dcoord, fderiv_clm_apply hd (differentiableAt_const _),
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    fderiv_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.map_zero, ContinuousLinearMap.flip_apply, zero_add]
  exact hf.isSymmSndFDerivAt (by norm_num) (basis i) (basis j)

theorem partial_laplacian (f : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (i : Fin 3) :
    dcoord (laplacian f) x i = laplacian (fun y => dcoord f y i) x := by
  have hd (j k : Fin 3) := (partial_smooth (partial_smooth hf j) k).differentiableAt (by simp)
  have hc (j : Fin 3) :
      dcoord (fun y => dcoord (fun z => dcoord f z j) y j) x i =
        dcoord (fun y => dcoord (fun z => dcoord f z i) y j) x j := by
    rw [partial_comm_at (partial_smooth hf j) i j]
    apply partial_congr
    have hf2 : ContDiffAt ℝ 2 f x :=
      hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    filter_upwards [hf2.eventually (by norm_num)] with y hy
    exact partial_comm_two hy i j
  unfold laplacian
  simp only [Fin.sum_univ_three]
  rw [partial_add ((hd 0 0).add (hd 1 1)) (hd 2 2),
    partial_add (hd 0 0) (hd 1 1), hc 0, hc 1, hc 2]

theorem laplacian_sub (f g : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    laplacian (fun y => f y-g y) x = laplacian f x-laplacian g x := by
  have hs (i : Fin 3) :
      dcoord (fun y => dcoord (fun z => f z-g z) y i) x i =
        dcoord (fun y => dcoord f y i) x i-dcoord (fun y => dcoord g y i) x i := by
    have he : (fun y => dcoord (fun z => f z-g z) y i) =ᶠ[𝓝 x]
        (fun y => dcoord f y i-dcoord g y i) := by
      have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
      have hg1 : ContDiffAt ℝ 1 g x := hg.of_le (by simp)
      filter_upwards [hf1.eventually (by norm_num), hg1.eventually (by norm_num)] with y hy hz
      exact partial_sub (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num)) i
    rw [partial_congr he, partial_sub
      ((partial_smooth hf i).differentiableAt (by simp))
      ((partial_smooth hg i).differentiableAt (by simp))]
  simp only [laplacian, hs, Fin.sum_univ_three]
  ring

theorem laplacian_curl (A : Field) (x : Space)
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x) (i : Fin 3) :
    laplacian (fun y => curl A y i) x =
      curl (fun y j => laplacian (fun z => A z j) y) x i := by
  fin_cases i <;> dsimp [curl, pd] <;>
    rw [laplacian_sub _ _ x (partial_smooth (hA _) _) (partial_smooth (hA _) _),
      ← partial_laplacian _ _ (hA _), ← partial_laplacian _ _ (hA _)]

theorem divergence_curl_at (A : Field) (x : Space)
    (hA : ∀ j, ContDiffAt ℝ (⊤ : ℕ∞) (fun y => A y j) x) :
    divergence (curl A) x = 0 := by
  have hd (j l : Fin 3) := (partial_smooth (hA j) l).differentiableAt (by simp)
  dsimp [divergence, curl, pd]
  rw [partial_sub (hd 2 1) (hd 1 2), partial_sub (hd 0 2) (hd 2 0),
    partial_sub (hd 1 0) (hd 0 1),
    partial_comm_at (hA 2) 0 1, partial_comm_at (hA 1) 0 2,
    partial_comm_at (hA 0) 1 2]
  ring

theorem laplacian_coordinate (j : Fin 3) (x : Space) :
    laplacian (fun y : Space => (y j : ℂ)) x = 0 := by
  simp only [laplacian, coordinate_partial]
  simp [dcoord]

def radialVector (f : Space → ℂ) : Field := fun x j => (x j : ℂ)*f x
def toroidal (f : Space → ℂ) : Field := curl (radialVector f)

theorem radialVector_smooth (f : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (j : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => radialVector f y j) x :=
  (coordinate j).contDiff.contDiffAt.mul hf

theorem toroidal_smooth (f : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (j : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => toroidal f y j) x :=
  curl_smooth _ (radialVector_smooth f x hf) j

theorem radialVector_laplacian (f : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (j : Fin 3) :
    laplacian (fun y => radialVector f y j) x =
      (x j : ℂ)*laplacian f x+2*dcoord f x j := by
  change laplacian (fun y => (y j : ℂ)*f y) x = _
  have hj : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => (y j : ℂ)) x :=
    (coordinate j).contDiff.contDiffAt
  rw [laplacian_mul _ _ x hj hf,
    laplacian_coordinate]
  simp only [coordinate_partial, mul_zero, add_zero]
  simp

theorem curl_congr {A B : Field} {x : Space}
    (h : ∀ j, (fun y => A y j) =ᶠ[𝓝 x] (fun y => B y j)) : curl A x = curl B x := by
  have hd (i j : Fin 3) := partial_congr (h j) i
  simp only [curl, pd, hd]

theorem laplacian_smooth (f : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ContDiffAt ℝ (⊤ : ℕ∞) (laplacian f) x := by
  have hs (i : Fin 3) := partial_smooth (partial_smooth hf i) i
  unfold laplacian
  simpa only [laplacian, Fin.sum_univ_three] using ((hs 0).add (hs 1)).add (hs 2)

theorem toroidal_laplacian {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℂ)
    (hf : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f y) (x : Space) (hx : x ∈ Ω) (i : Fin 3) :
    laplacian (fun y => toroidal f y i) x = toroidal (laplacian f) x i := by
  change laplacian (fun y => curl (radialVector f) y i) x = _
  rw [laplacian_curl _ x (radialVector_smooth f x (hf x hx))]
  have he : curl (fun y j => laplacian (fun z => radialVector f z j) y) x =
      curl (fun y j => radialVector (laplacian f) y j+2*gradient f y j) x := by
    apply curl_congr
    intro j
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact radialVector_laplacian f y (hf y hy) j
  rw [he, curl_add (radialVector (laplacian f)) (fun y j => 2*gradient f y j) x
    (fun j => (radialVector_smooth (laplacian f) x (laplacian_smooth f x (hf x hx)) j).differentiableAt (by simp))
    (fun j => ((partial_smooth (hf x hx) j).differentiableAt (by simp)).const_mul 2),
    curl_const_mul (gradient f) x 2
      (fun j => (partial_smooth (hf x hx) j).differentiableAt (by simp)),
    curl_gradient_at (hf x hx)]
  simp only [Pi.zero_apply, mul_zero, add_zero, toroidal]

theorem toroidal_helmholtz {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℂ)
    (hf : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f y) (q : ℂ)
    (hHelm : ∀ y ∈ Ω, laplacian f y+q^2*f y=0) (x : Space) (hx : x ∈ Ω) (i : Fin 3) :
    laplacian (fun y => toroidal f y i) x+q^2*toroidal f x i=0 := by
  rw [toroidal_laplacian hΩ f hf x hx]
  have he : toroidal (laplacian f) x = fun j => -(q^2)*toroidal f x j := by
    change curl (radialVector (laplacian f)) x = _
    have hc : curl (radialVector (laplacian f)) x =
        curl (fun y j => -(q^2)*radialVector f y j) x := by
      apply curl_congr
      intro j
      filter_upwards [hΩ.mem_nhds hx] with y hy
      dsimp [radialVector]
      linear_combination (y j : ℂ)*hHelm y hy
    rw [hc, curl_const_mul _ x _
      (fun j => (radialVector_smooth f x (hf x hx) j).differentiableAt (by simp))]
    rfl
  rw [he]
  ring

theorem toroidal_curl_curl {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℂ)
    (hf : ∀ y ∈ Ω, ContDiffAt ℝ (⊤ : ℕ∞) f y) (q : ℂ)
    (hHelm : ∀ y ∈ Ω, laplacian f y+q^2*f y=0) (x : Space) (hx : x ∈ Ω) (i : Fin 3) :
    curl (curl (toroidal f)) x i = q^2*toroidal f x i := by
  rw [curl_curl_laplacian _ x (toroidal_smooth f x (hf x hx))]
  have hz : divergence (toroidal f) =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact divergence_curl_at _ y (radialVector_smooth f y (hf y hy))
  rw [partial_congr hz]
  have hd : dcoord (fun _ : Space => (0 : ℂ)) x i = 0 := by simp [dcoord]
  rw [hd]
  linear_combination -(toroidal_helmholtz hΩ f hf q hHelm x hx i)

end OQ14.DebyeCalculus

#print axioms OQ14.DebyeCalculus.partial_congr
#print axioms OQ14.DebyeCalculus.partial_comm_two
#print axioms OQ14.DebyeCalculus.partial_laplacian
#print axioms OQ14.DebyeCalculus.laplacian_sub
#print axioms OQ14.DebyeCalculus.laplacian_curl
#print axioms OQ14.DebyeCalculus.divergence_curl_at
#print axioms OQ14.DebyeCalculus.laplacian_coordinate
#print axioms OQ14.DebyeCalculus.radialVector_smooth
#print axioms OQ14.DebyeCalculus.toroidal_smooth
#print axioms OQ14.DebyeCalculus.radialVector_laplacian
#print axioms OQ14.DebyeCalculus.curl_congr
#print axioms OQ14.DebyeCalculus.laplacian_smooth
#print axioms OQ14.DebyeCalculus.toroidal_laplacian
#print axioms OQ14.DebyeCalculus.toroidal_helmholtz
#print axioms OQ14.DebyeCalculus.toroidal_curl_curl
