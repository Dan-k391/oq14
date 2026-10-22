import ConicalWeakGradient

/-! The actual conical weak gradient has vanishing distributional curl. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalWeakCurl
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalCapField
open scoped Topology

theorem mixed_partial_comm (ψ : Space → ℝ) (hψ : ContDiff ℝ 2 ψ) (x : Space) (i j : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ ψ y (basis j)) x (basis i) =
      fderiv ℝ (fun y => fderiv ℝ ψ y (basis i)) x (basis j) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ ψ) :=
    (contDiff_succ_iff_fderiv (n := 1)).mp hψ |>.2.2
  have he (i j : Fin 3) : fderiv ℝ (fun y => fderiv ℝ ψ y (basis j)) x (basis i) =
      fderiv ℝ (fderiv ℝ ψ) x (basis i) (basis j) := by
    simp [fderiv_clm_apply (hd.differentiable (by simp) x) (differentiableAt_const (basis j))]
  rw [he,he]
  exact hψ.contDiffAt.isSymmSndFDerivAt (by simp) (basis i) (basis j)

theorem weak_cross_pair (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (ψ : Space → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hcompact : HasCompactSupport ψ) (i j : Fin 3) :
    (∫ x : Space, electric ν a t x i*fderiv ℝ ψ x (basis j)) =
      ∫ x : Space, electric ν a t x j*fderiv ℝ ψ x (basis i) := by
  have hp (j : Fin 3) : ContDiff ℝ 1 (fun x => fderiv ℝ ψ x (basis j)) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ ψ) :=
      (contDiff_succ_iff_fderiv (n := 1)).mp hψ |>.2.2
    exact hd.clm_apply contDiff_const
  have hi := ConicalWeakGradient.weak_partial ν a t hν ha ht ht1 i
    (fun x => fderiv ℝ ψ x (basis j)) (hp j) (hcompact.fderiv_apply ℝ (basis j))
  have hj := ConicalWeakGradient.weak_partial ν a t hν ha ht ht1 j
    (fun x => fderiv ℝ ψ x (basis i)) (hp i) (hcompact.fderiv_apply ℝ (basis i))
  have hleft : (∫ x : Space, potential ν a t x*
      fderiv ℝ (fun y => fderiv ℝ ψ y (basis j)) x (basis i)) =
      ∫ x : Space, potential ν a t x*fderiv ℝ (fun y => fderiv ℝ ψ y (basis i)) x (basis j) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [mixed_partial_comm ψ hψ x i j]
  linarith

def weakCurlPairing (ν a t : ℝ) (ψ : Space → ℝ) : Space :=
  !₂[(∫ x, electric ν a t x 2*fderiv ℝ ψ x (basis 1))-
       ∫ x, electric ν a t x 1*fderiv ℝ ψ x (basis 2),
     (∫ x, electric ν a t x 0*fderiv ℝ ψ x (basis 2))-
       ∫ x, electric ν a t x 2*fderiv ℝ ψ x (basis 0),
     (∫ x, electric ν a t x 1*fderiv ℝ ψ x (basis 0))-
       ∫ x, electric ν a t x 0*fderiv ℝ ψ x (basis 1)]

theorem weak_curl_zero (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (ψ : Space → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hcompact : HasCompactSupport ψ) : weakCurlPairing ν a t ψ = 0 := by
  ext i
  fin_cases i
  · change (∫ x, electric ν a t x 2*fderiv ℝ ψ x (basis 1))-
        (∫ x, electric ν a t x 1*fderiv ℝ ψ x (basis 2)) = 0
    rw [weak_cross_pair ν a t hν ha ht ht1 ψ hψ hcompact 2 1,sub_self]
  · change (∫ x, electric ν a t x 0*fderiv ℝ ψ x (basis 2))-
        (∫ x, electric ν a t x 2*fderiv ℝ ψ x (basis 0)) = 0
    rw [weak_cross_pair ν a t hν ha ht ht1 ψ hψ hcompact 0 2,sub_self]
  · change (∫ x, electric ν a t x 1*fderiv ℝ ψ x (basis 0))-
        (∫ x, electric ν a t x 0*fderiv ℝ ψ x (basis 1)) = 0
    rw [weak_cross_pair ν a t hν ha ht ht1 ψ hψ hcompact 1 0,sub_self]

end OQ14.ConicalWeakCurl

#print axioms OQ14.ConicalWeakCurl.mixed_partial_comm
#print axioms OQ14.ConicalWeakCurl.weak_cross_pair
#print axioms OQ14.ConicalWeakCurl.weak_curl_zero
