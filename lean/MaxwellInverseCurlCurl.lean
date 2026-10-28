import MaterialHCurl
import WeakPoynting.LocalRegularity

/-! The actual magnetic curl-curl equation with inverse dielectric weight. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.MaxwellInverseCurlCurl
open MeasureTheory OQ14.Maxwell
open scoped Topology

theorem inverse_curl_representation {Ω : Set Space} (k : ℝ) (ε : Space → ℝ)
    (hε : ∀ x, 0 < ε x) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) ε E H) :
    ∃ W : DomainCurl.L2Vector Ω,
      DomainCurl.HasWeakCurl Ω W ((k^2 : ℂ) • H.val.1) ∧
      ∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
        W j x = (((ε x)⁻¹ : ℝ) : ℂ) * H.val.2 j x := by
  let W : DomainCurl.L2Vector Ω := (-(Complex.I*(k : ℂ))) • E.val.1
  have hcurl : E.val.2 = (Complex.I*(k : ℂ)) • H.val.1 := by
    funext j
    apply MeasureTheory.Lp.ext
    filter_upwards [hM.1, MeasureTheory.Lp.coeFn_smul (Complex.I*(k : ℂ)) (H.val.1 j)] with x hx hs
    change E.val.2 j x = (((Complex.I*(k : ℂ)) • H.val.1 j : DomainCurl.L2Scalar Ω) : Space → ℂ) x
    rw [hs]
    simpa using hx j
  have hgraph := (DomainCurl.graph Ω).smul_mem (-(Complex.I*(k : ℂ))) E.property
  have hgraph' : DomainCurl.HasWeakCurl Ω W ((k^2 : ℂ) • H.val.1) := by
    change DomainCurl.HasWeakCurl Ω ((-(Complex.I*(k : ℂ))) • E.val.1)
      ((-(Complex.I*(k : ℂ))) • E.val.2) at hgraph
    rw [hcurl, smul_smul] at hgraph
    convert hgraph using 1; congr 1; ring_nf; simp
  refine ⟨W,hgraph',?_⟩
  apply ae_all_iff.mpr
  intro j
  filter_upwards [hM.2, MeasureTheory.Lp.coeFn_smul (-(Complex.I*(k : ℂ))) (E.val.1 j)] with x hx hw
  change (((-(Complex.I*(k : ℂ))) • E.val.1 j : DomainCurl.L2Scalar Ω) : Space → ℂ) x = _
  rw [hw, hx j]
  have hn : (ε x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hε x).ne'
  push_cast
  field_simp
  ring

theorem magnetic_h1_and_curlcurl {Ω K : Set Space} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) (k : ℝ) (hk : k ≠ 0)
    (ε : Space → ℝ) (hε : ∀ x, 0 < ε x) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) ε E H) :
    ∃ (W : DomainCurl.L2Vector Ω) (U : Set Space) (F : WeakCurl.L2Vector)
      (G : DivCurlRegularity.DerivativeIndex → WeakCurl.L2Scalar),
      DomainCurl.HasWeakCurl Ω W ((k^2 : ℂ) • H.val.1) ∧
      (∀ᵐ x ∂DomainCurl.regionMeasure Ω, ∀ j : Fin 3,
        W j x = (((ε x)⁻¹ : ℝ) : ℂ) * H.val.2 j x) ∧
      IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧
      (∀ q, DivCurlCompact.HasWeakPartial (F q.2) (G q) q.1) ∧
      (∀ j, (fun x => F j x) =ᵐ[volume.restrict U] (fun x => H.val.1 j x)) := by
  obtain ⟨W,hW,hWae⟩ := inverse_curl_representation k ε hε E H hM
  obtain ⟨U,F,G,hU,hKU,hUΩ,hG,hF⟩ :=
    LocalRegularity.maxwell_magnetic_local_h1 hΩ hK hKΩ k hk ε E H hM
  exact ⟨W,U,F,G,hW,hWae,hU,hKU,hUΩ,hG,hF⟩

theorem inverse_weight_coercivity {Ω : Set Space} (ε : Space → ℝ) (M : ℝ)
    (hεm : Measurable ε) (hε1 : ∀ x, 1 ≤ ε x) (hεM : ∀ x, ε x ≤ M)
    (f : Space → ℂ) (hf : MemLp f 2 (DomainCurl.regionMeasure Ω)) :
    M⁻¹ * (∫ x in Ω, ‖f x‖^2) ≤ ∫ x in Ω, (ε x)⁻¹ * ‖f x‖^2 := by
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one ((hε1 0).trans (hεM 0))
  have hfi : Integrable (fun x => ‖f x‖^2) (DomainCurl.regionMeasure Ω) :=
    hf.integrable_norm_pow (by norm_num)
  have hweighted : Integrable (fun x => (ε x)⁻¹ * ‖f x‖^2) (DomainCurl.regionMeasure Ω) := by
    apply hfi.mono'
    · exact (hεm.inv.aestronglyMeasurable.mul (hf.aestronglyMeasurable.norm.pow 2))
    · filter_upwards with x
      have hpos : 0 < ε x := lt_of_lt_of_le zero_lt_one (hε1 x)
      have hinv : (ε x)⁻¹ ≤ 1 := (inv_le_one₀ hpos).2 (hε1 x)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hpos.le) (sq_nonneg _))]
      exact mul_le_of_le_one_left (sq_nonneg _) hinv
  rw [← integral_const_mul]
  apply integral_mono_ae (hfi.const_mul _) hweighted
  filter_upwards with x
  exact mul_le_mul_of_nonneg_right (inv_le_inv₀ hM (lt_of_lt_of_le zero_lt_one (hε1 x)) |>.2 (hεM x)) (sq_nonneg _)

end OQ14.MaxwellInverseCurlCurl
#print axioms OQ14.MaxwellInverseCurlCurl.inverse_curl_representation
#print axioms OQ14.MaxwellInverseCurlCurl.magnetic_h1_and_curlcurl
#print axioms OQ14.MaxwellInverseCurlCurl.inverse_weight_coercivity
