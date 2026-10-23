import ConicalPlaneWaves

/-! Actual finite entire Maxwell illuminations representing the Runge approximants. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalFinitePlanes
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalRungeBall OQ14.ConicalRungeClosure
open scoped InnerProductSpace ComplexConjugate Topology
abbrev Space := Maxwell.Space

def electric (k : ℝ) (c : WaveIndex →₀ ℂ) : Field :=
  fun x j => c.sum (fun w b => b*ConicalPlaneWaves.electric k (w.1 : Space) w.2 x j)

def magnetic (k : ℝ) (c : WaveIndex →₀ ℂ) : Field :=
  fun x j => c.sum (fun w b => b*ConicalPlaneWaves.magnetic k (w.1 : Space) w.2 x j)

def restricted (k a : ℝ) (c : WaveIndex →₀ ℂ) : BallL2 a := c.sum (fun w b => b • waves k a w)

theorem electric_smooth (k : ℝ) (c : WaveIndex →₀ ℂ) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => electric k c x j) :=
  ContDiff.sum (fun w _ => contDiff_const.mul (ConicalPlaneWaves.electric_smooth k (w.1 : Space) w.2 j))

theorem magnetic_smooth (k : ℝ) (c : WaveIndex →₀ ℂ) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => magnetic k c x j) :=
  ContDiff.sum (fun w _ => contDiff_const.mul (ConicalPlaneWaves.magnetic_smooth k (w.1 : Space) w.2 j))

private theorem curl_sum {ι : Type*} (s : Finset ι) (F : ι → Field) (A : ι → ℂ) (x : Space)
    (hF : ∀ w i, DifferentiableAt ℝ (fun y => F w y i) x) (i : Fin 3) :
    curl (fun y j => ∑ w ∈ s, A w*F w y j) x i=∑ w ∈ s, A w*curl (F w) x i := by
  have hp (a b : Fin 3) : dcoord (fun y => ∑ w ∈ s, A w*F w y b) x a=
      ∑ w ∈ s, A w*dcoord (fun y => F w y b) x a := by
    unfold dcoord
    rw [fderiv_sum (fun w _ => (hF w b).const_mul (A w))]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro w _
    exact partial_const_mul (hF w b) (A w) a
  have hc (G : Field) : curl G x i=dcoord (fun y => G y (WeakCurl.previous i)) x (WeakCurl.next i)-
      dcoord (fun y => G y (WeakCurl.next i)) x (WeakCurl.previous i) := by fin_cases i <;> rfl
  rw [hc,hp,hp,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [hc]
  ring

theorem maxwell_at (k : ℝ) (c : WaveIndex →₀ ℂ) (x : Space) : MaxwellAt k 1 1 (electric k c) (magnetic k c) x := by
  constructor
  · ext i
    change curl (fun y j => ∑ w ∈ c.support, c w*ConicalPlaneWaves.electric k (w.1 : Space) w.2 y j) x i=_
    rw [curl_sum _ _ c x (fun w j => (ConicalPlaneWaves.electric_smooth k (w.1 : Space) w.2 j).differentiable (by simp) x)]
    simp_rw [(ConicalPlaneWaves.maxwell_at k _ (AngularPower.sphere_norm _) _ x).1]
    simp only [magnetic,Finsupp.sum,Complex.ofReal_one,mul_one,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  · ext i
    change curl (fun y j => ∑ w ∈ c.support, c w*ConicalPlaneWaves.magnetic k (w.1 : Space) w.2 y j) x i=_
    rw [curl_sum _ _ c x (fun w j => (ConicalPlaneWaves.magnetic_smooth k (w.1 : Space) w.2 j).differentiable (by simp) x)]
    simp_rw [(ConicalPlaneWaves.maxwell_at k _ (AngularPower.sphere_norm _) _ x).2]
    simp only [electric,Finsupp.sum,Complex.ofReal_one,mul_one,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring

private theorem restriction_sum_ae (k a : ℝ) (s : Finset WaveIndex) (b : WaveIndex → ℂ) (j : Fin 3) :
    ((∑ w ∈ s, b w • waves k a w) j : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      fun x => ∑ w ∈ s, b w*ConicalPlaneWaves.electric k (w.1 : Space) w.2 x j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty,PiLp.zero_apply] using Lp.coeFn_zero ℂ 2 (volume.restrict (closedBall (0 : Space) a))
  | @insert w s hws ih =>
    simp only [Finset.sum_insert hws]
    filter_upwards [Lp.coeFn_add (b w • waves k a w j) ((∑ v ∈ s, b v • waves k a v) j),
      Lp.coeFn_smul (b w) (waves k a w j),
      (wave_memLp k a (w.1 : Space) w.2 j).coeFn_toLp,ih] with x hadd hsmul hw hs
    change ((b w • waves k a w j)+((∑ v ∈ s, b v • waves k a v) j)) x=_
    rw [hadd]
    simp only [Pi.add_apply,hsmul,Pi.smul_apply,smul_eq_mul,hs]
    change b w*((wave_memLp k a (w.1 : Space) w.2 j).toLp _) x+_= _
    rw [hw,ConicalPlaneWaves.electric_eq_waveValue]

theorem restricted_ae (k a : ℝ) (c : WaveIndex →₀ ℂ) (j : Fin 3) :
    (restricted k a c j : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => electric k c x j :=
  restriction_sum_ae k a c.support c j

theorem electric_memLp_ball (k a : ℝ) (c : WaveIndex →₀ ℂ) (j : Fin 3) :
    MemLp (fun x => electric k c x j) 2 (volume.restrict (closedBall (0 : Space) a)) :=
  (Lp.memLp (restricted k a c j)).ae_eq (restricted_ae k a c j)

theorem finite_illumination_approximation (k : ℝ) (hk : 0 < k) (a T : ℝ) (ha : 0 ≤ a) (haT : a ≤ T)
    (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hσin : ∀ j x, x ∈ closedBall (0 : Space) a → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : WaveIndex →₀ ℂ, (∀ x, MaxwellAt k 1 1 (electric k c) (magnetic k c) x) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => electric k c x j)) ∧
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => magnetic k c x j)) ∧
      ‖restricted k a c-target k a T G σ hcσ hG‖ < ε := by
  obtain ⟨c,hc⟩ := ConicalRungeClosure.finite_approximation k hk a T ha haT G σ hcσ hσin hG ε hε
  exact ⟨c,maxwell_at k c,electric_smooth k c,magnetic_smooth k c,hc⟩

end OQ14.ConicalFinitePlanes

#print axioms OQ14.ConicalFinitePlanes.electric_smooth
#print axioms OQ14.ConicalFinitePlanes.magnetic_smooth
#print axioms OQ14.ConicalFinitePlanes.maxwell_at
#print axioms OQ14.ConicalFinitePlanes.restricted_ae
#print axioms OQ14.ConicalFinitePlanes.electric_memLp_ball
#print axioms OQ14.ConicalFinitePlanes.finite_illumination_approximation
