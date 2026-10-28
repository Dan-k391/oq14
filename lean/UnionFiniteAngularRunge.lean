import UnionFreeRunge
import FiniteAngularHerglotz
import ConicalUniformBall

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.UnionFiniteAngularRunge
open MeasureTheory Set Metric OQ14.Maxwell OQ14.UnionFreeRunge
open scoped ENNReal Topology
abbrev Space := Maxwell.Space
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex

def factor (K : Set Space) [IsFiniteMeasure (volume.restrict K)] : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => Scalar K)).symm.toContinuousLinearMap‖*
    (measureUnivNNReal (volume.restrict K) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹

theorem factor_nonnegative (K : Set Space) [IsFiniteMeasure (volume.restrict K)] : 0 ≤ factor K :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (NNReal.coe_nonneg _) _)

theorem norm_bound (K : Set Space) [IsFiniteMeasure (volume.restrict K)] (g : Vector K) (e : ℝ) (he : 0 ≤ e)
    (hg : ∀ i, ∀ᵐ x : Space ∂volume.restrict K, ‖g i x‖ ≤ e) : ‖g‖ ≤ factor K*e := by
  let A := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => Scalar K)).symm.toContinuousLinearMap
  let M : ℝ := (measureUnivNNReal (volume.restrict K) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  have hM : 0 ≤ M := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hpi : ‖fun i => g i‖ ≤ M*e := (pi_norm_le_iff_of_nonneg (mul_nonneg hM he)).mpr
    (fun i => Lp.norm_le_of_ae_bound he (hg i))
  have h := (A.le_opNorm (fun i => g i)).trans (mul_le_mul_of_nonneg_left hpi (norm_nonneg A))
  change ‖g‖ ≤ _ at h
  exact h.trans_eq (by dsimp only [factor,A,M]; ring)

theorem incident_memLp (k R : ℝ) (K : Set Space) (hKR : K ⊆ closedBall (0 : Space) R)
    (d : ModeIndex →₀ ℂ) (i : Fin 3) :
    MemLp (fun x => (FiniteAngularHerglotz.incident k d).E x i) 2 (volume.restrict K) :=
  (SmallVolumeMaxwell.continuous_memLp_ball _ ((FiniteAngularHerglotz.incident k d).smoothE i).continuous R).mono_measure
    (Measure.restrict_mono_set volume hKR)

def incident (k R : ℝ) (K : Set Space) (hKR : K ⊆ closedBall (0 : Space) R) (d : ModeIndex →₀ ℂ) : Vector K :=
  (WithLp.equiv 2 (Fin 3 → Scalar K)).symm (fun i =>
    (incident_memLp k R K hKR d i).toLp (fun x => (FiniteAngularHerglotz.incident k d).E x i))

theorem incident_ae (k R : ℝ) (K : Set Space) (hKR : K ⊆ closedBall (0 : Space) R)
    (d : ModeIndex →₀ ℂ) (i : Fin 3) :
    (incident k R K hKR d i : Space → ℂ) =ᵐ[volume.restrict K] fun x => (FiniteAngularHerglotz.incident k d).E x i :=
  (incident_memLp k R K hKR d i).coeFn_toLp

def planes (k : ℝ) (K : Set Space) [IsFiniteMeasure (volume.restrict K)] (c : WaveIndex →₀ ℂ) : Vector K :=
  c.sum (fun w b => b • wave k K w)

theorem planes_ae (k : ℝ) (K : Set Space) [IsFiniteMeasure (volume.restrict K)]
    (c : WaveIndex →₀ ℂ) (j : Fin 3) :
    (planes k K c j : Space → ℂ) =ᵐ[volume.restrict K] fun x => ConicalFinitePlanes.electric k c x j := by
  classical
  have h (s : Finset WaveIndex) (b : WaveIndex → ℂ) :
      ((∑ w ∈ s, b w • wave k K w) j : Space → ℂ) =ᵐ[volume.restrict K]
        fun x => ∑ w ∈ s, b w * ConicalPlaneWaves.electric k (w.1 : Space) w.2 x j := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty,PiLp.zero_apply] using Lp.coeFn_zero ℂ 2 (volume.restrict K)
    | @insert w s hws ih =>
      simp only [Finset.sum_insert hws]
      filter_upwards [Lp.coeFn_add (b w • wave k K w j) ((∑ v ∈ s, b v • wave k K v) j),
        Lp.coeFn_smul (b w) (wave k K w j), (wave_memLp k K w j).coeFn_toLp,ih] with x hadd hsmul hw hs
      change ((b w • wave k K w j)+((∑ v ∈ s, b v • wave k K v) j)) x=_
      rw [hadd]
      simp only [Pi.add_apply,hsmul,Pi.smul_apply,smul_eq_mul,hs]
      change b w*((wave_memLp k K w j).toLp _) x+_= _
      rw [hw,ConicalPlaneWaves.electric_eq_waveValue]
  exact h c.support c

theorem approximation {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i + radius j < dist (center i) (center j))
    (k : ℝ) (hk : 0 < k) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hKR : balls center radius ⊆ closedBall (0 : Space) R)
    (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hiσ : ∀ j x, x ∈ balls center radius → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ d : ModeIndex →₀ ℂ, ‖incident k R (balls center radius) hKR d-
      target k R T (balls center radius) hKR G σ hcσ hG‖ < ε := by
  let K := balls center radius
  let δ := ε / (2*(factor K+1))
  have hδ : 0 < δ := div_pos hε (by have := factor_nonnegative K; positivity)
  obtain ⟨c,hc⟩ := finite_union_approximation center radius hr hsep k hk R T hR hRT hKR G σ hcσ hiσ hG (ε/2) (by positivity)
  obtain ⟨d,hd⟩ := FiniteAngularHerglotz.uniform_plane_approximation k R c δ hδ
  refine ⟨d,?_⟩
  have hdiff : ‖incident k R K hKR d-planes k K c‖ ≤ factor K*δ := by
    apply norm_bound K _ δ hδ.le
    intro i
    filter_upwards [Lp.coeFn_sub (incident k R K hKR d i) (planes k K c i),
      incident_ae k R K hKR d i, planes_ae k K c i,
      ae_restrict_mem (balls_compact center radius).measurableSet] with x hs hi hp hx
    change ‖(incident k R K hKR d i-planes k K c i) x‖ ≤ δ
    rw [hs]
    simpa only [Pi.sub_apply,hi,hp] using (hd x (hKR hx) i).le
  have he : incident k R K hKR d-target k R T K hKR G σ hcσ hG =
      (incident k R K hKR d-planes k K c)+(planes k K c-target k R T K hKR G σ hcσ hG) := by abel
  rw [he]
  apply (norm_add_le _ _).trans_lt
  have hfactor := factor_nonnegative K
  have hδeq : (factor K+1)*δ = ε/2 := by dsimp [δ]; field_simp; ring
  dsimp [planes] at hdiff ⊢
  change ‖(c.sum fun w b => b • wave k K w)-target k R T K hKR G σ hcσ hG‖ < ε/2 at hc
  nlinarith
end OQ14.UnionFiniteAngularRunge
#print axioms OQ14.UnionFiniteAngularRunge.factor_nonnegative
#print axioms OQ14.UnionFiniteAngularRunge.norm_bound
#print axioms OQ14.UnionFiniteAngularRunge.incident_memLp
#print axioms OQ14.UnionFiniteAngularRunge.incident_ae
#print axioms OQ14.UnionFiniteAngularRunge.planes_ae
#print axioms OQ14.UnionFiniteAngularRunge.approximation

