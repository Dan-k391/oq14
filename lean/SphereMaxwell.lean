import SphereMagneticKernel

/-! Both actual global Maxwell curl identities of the literal sphere-integral J/K pair. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereMaxwell
open MeasureTheory Metric Set SphereReactionKernel SphereWaveCalculus SphereMagneticKernel
open Maxwell (dcoord basis partial_const_mul curl pd MaxwellAt)
open WeakCurl (next previous)
open scoped Topology

theorem K_partial (k : ℝ) (x : Space) (a i j : Fin 3) :
    dcoord (fun y => K k y i j) x a =
      ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*(Complex.I*(k : ℂ))*
        moment (fun θ => transverse i j θ*coordinate a θ) k x := by
  change dcoord (fun y => ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*moment (transverse i j) k y) x a = _
  rw [partial_const_mul (moment_hasFDerivAt _ (transverse_continuous i j) 2
    (transverse_bound i j) k x).differentiableAt,
    moment_partial _ (transverse_continuous i j) 2 (transverse_bound i j)]
  simp only [coordinate, mul_assoc]

theorem angular_curl (θ : Sphere) (i j : Fin 3) :
    transverse (previous i) j θ*coordinate (next i) θ-
      transverse (next i) j θ*coordinate (previous i) θ = -amplitude θ i j := by
  have hs : (coordinate 0 θ)^2+(coordinate 1 θ)^2+(coordinate 2 θ)^2=1 := by
    simpa only [coordinate, sphere_norm, Complex.ofReal_one, one_pow] using GreenKernel.coordinate_squares θ.val
  simp only [coordinate] at hs
  fin_cases i <;> fin_cases j <;> simp [transverse, coordinate, amplitude, next, previous, Fin.ext_iff]
  all_goals ring_nf
  all_goals linear_combination -hs

theorem curl_K (k : ℝ) (x : Space) (i j : Fin 3) :
    curl (fun y a => K k y a j) x i = -(Complex.I*(k : ℂ))*J k x i j := by
  have he : curl (fun y a => K k y a j) x i =
      dcoord (fun y => K k y (previous i) j) x (next i)-
        dcoord (fun y => K k y (next i) j) x (previous i) := by fin_cases i <;> rfl
  rw [he, K_partial, K_partial]
  have hi (a b : Fin 3) : Integrable (fun θ : Sphere =>
      (transverse a j θ*coordinate b θ)*wave k x θ) surface :=
    moment_integrable _ ((transverse_continuous a j).mul (coordinate_continuous b)) 2
      (fun θ => by
        rw [norm_mul]
        exact (mul_le_mul (transverse_bound a j θ) (coordinate_bound b θ) (norm_nonneg _)
          (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by norm_num)) k x
  have hm : moment (fun θ => transverse (previous i) j θ*coordinate (next i) θ) k x-
      moment (fun θ => transverse (next i) j θ*coordinate (previous i) θ) k x =
        -moment (fun θ => amplitude θ i j) k x := by
    unfold moment
    rw [← integral_sub (hi _ _) (hi _ _), ← integral_neg]
    apply integral_congr_ae
    filter_upwards with θ
    rw [← sub_mul, angular_curl]
    ring
  unfold J
  calc
    _ = ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*(Complex.I*(k : ℂ))*
      (moment (fun θ => transverse (previous i) j θ*coordinate (next i) θ) k x-
        moment (fun θ => transverse (next i) j θ*coordinate (previous i) θ) k x) := by ring
    _ = _ := by rw [hm]; unfold moment; ring

theorem maxwell (k : ℝ) (j : Fin 3) (x : Space) :
    MaxwellAt k 1 1 (fun y i => J k y i j) (fun y i => K k y i j) x := by
  constructor
  · funext i
    simpa only [Complex.ofReal_one, mul_one] using curl_J k x i j
  · funext i
    simpa only [Complex.ofReal_one, mul_one, neg_mul] using curl_K k x i j

end OQ14.SphereMaxwell
#print axioms OQ14.SphereMaxwell.K_partial
#print axioms OQ14.SphereMaxwell.angular_curl
#print axioms OQ14.SphereMaxwell.curl_K
#print axioms OQ14.SphereMaxwell.maxwell
