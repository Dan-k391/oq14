import WeakPoynting.DivCurlCompact

/-! # Actual L2 weak derivatives from L2 curl and divergence -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.DivCurlRegularity

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurl OQ14.DivCurlCompact Filter
open scoped Topology SchwartzMap

abbrev SchwartzField := Fin 3 → 𝓢(Space, ℂ)
abbrev DerivativeIndex := Fin 3 × Fin 3

def partialL2 (f : SchwartzField) (p : DerivativeIndex) : L2Scalar :=
  FourierL2.embed (GradientProjection.pderivative p.1 (f p.2))

def curlL2 (f : SchwartzField) : L2Vector :=
  fun j => FourierL2.embed (GradientProjection.curl f j)

def divL2 (f : SchwartzField) : L2Scalar :=
  FourierL2.embed (GradientProjection.divergence f)

def graphL2 (f : SchwartzField) : L2Vector × L2Scalar := (curlL2 f, divL2 f)

theorem partialL2_sub (f g : SchwartzField) (p : DerivativeIndex) :
    partialL2 (f - g) p = partialL2 f p - partialL2 g p := by
  simp [partialL2, GradientProjection.pderivative, map_sub]

theorem graphL2_sub (f g : SchwartzField) : graphL2 (f - g) = graphL2 f - graphL2 g := by
  apply Prod.ext
  · funext j
    fin_cases j <;>
      simp [graphL2, curlL2, GradientProjection.curl, GradientProjection.pderivative,
        map_sub] <;> abel
  · simp [graphL2, divL2, GradientProjection.divergence, GradientProjection.pderivative,
      map_sub, map_add]
    abel

/-- Each actual coordinate derivative is controlled by the genuine curl-div graph norm. -/
theorem partialL2_norm_le (f : SchwartzField) (p : DerivativeIndex) :
    ‖partialL2 f p‖ ≤ 2 * ‖graphL2 f‖ := by
  have hp : ‖partialL2 f p‖ ^ 2 ≤ ∑ q : DerivativeIndex, ‖partialL2 f q‖ ^ 2 :=
    Finset.single_le_sum (fun q _ => sq_nonneg ‖partialL2 f q‖) (Finset.mem_univ p)
  have he : (∑ q : DerivativeIndex, ‖partialL2 f q‖ ^ 2) =
      (∑ j : Fin 3, ‖curlL2 f j‖ ^ 2) + ‖divL2 f‖ ^ 2 :=
    schwartz_divcurl_energy f
  have hc (j : Fin 3) : ‖curlL2 f j‖ ≤ ‖graphL2 f‖ :=
    (norm_le_pi_norm (curlL2 f) j).trans (norm_fst_le (graphL2 f))
  have hd : ‖divL2 f‖ ≤ ‖graphL2 f‖ := norm_snd_le (graphL2 f)
  have hc2 (j : Fin 3) : ‖curlL2 f j‖ ^ 2 ≤ ‖graphL2 f‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hc j) 2
  have hd2 : ‖divL2 f‖ ^ 2 ≤ ‖graphL2 f‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [he, Fin.sum_univ_three] at hp
  have h0 := hc2 0
  have h1 := hc2 1
  have h2 := hc2 2
  have hn := norm_nonneg (graphL2 f)
  have hn' := norm_nonneg (partialL2 f p)
  nlinarith

theorem partialL2_dist_le (f g : SchwartzField) (p : DerivativeIndex) :
    dist (partialL2 f p) (partialL2 g p) ≤ 2 * dist (graphL2 f) (graphL2 g) := by
  simpa only [dist_eq_norm, partialL2_sub, graphL2_sub] using partialL2_norm_le (f - g) p

theorem partialL2_cauchy {f : ℕ → SchwartzField}
    (h : CauchySeq (fun n => graphL2 (f n))) (p : DerivativeIndex) :
    CauchySeq (fun n => partialL2 (f n) p) := by
  rw [Metric.cauchySeq_iff] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hb := partialL2_dist_le (f m) (f n) p
  have hs := hN m hm n hn
  linarith

theorem graph_tendsto {f : ℕ → SchwartzField} {C : L2Vector} {D : L2Scalar}
    (hC : ∀ j, Tendsto (fun n => curlL2 (f n) j) atTop (𝓝 (C j)))
    (hD : Tendsto (fun n => divL2 (f n)) atTop (𝓝 D)) :
    Tendsto (fun n => graphL2 (f n)) atTop (𝓝 (C, D)) :=
  (tendsto_pi_nhds.mpr hC).prodMk_nhds hD

/-- The derivative limits are obtained from completeness of actual scalar L2. -/
theorem exists_derivative_limits {f : ℕ → SchwartzField} {C : L2Vector} {D : L2Scalar}
    (hC : ∀ j, Tendsto (fun n => curlL2 (f n) j) atTop (𝓝 (C j)))
    (hD : Tendsto (fun n => divL2 (f n)) atTop (𝓝 D)) :
    ∃ G : DerivativeIndex → L2Scalar,
      ∀ p, Tendsto (fun n => partialL2 (f n) p) atTop (𝓝 (G p)) := by
  have hc := (graph_tendsto hC hD).cauchySeq
  exact Classical.axiomOfChoice (fun p => cauchySeq_tendsto_of_complete (partialL2_cauchy hc p))

/-- Compact support and genuine L2 curl/divergence suffice to construct every
actual L2 weak derivative. No differentiability assumption is imposed on E. -/
theorem compact_weak_derivatives {E C : L2Vector} {D : L2Scalar}
    (hE : ∀ j, CompactRepresentative (E j))
    (hC : HasWeakCurl E C) (hD : HasWeakDivergence E D) :
    ∃ G : DerivativeIndex → L2Scalar, ∀ p, HasWeakPartial (E p.2) (G p) p.1 := by
  obtain ⟨f, hf, hc, hd⟩ := compact_schwartz_graph_approximation hE hC hD
  obtain ⟨G, hG⟩ := exists_derivative_limits hc hd
  refine ⟨G, fun p => ?_⟩
  exact weakPartial_limit p.1 (hf p.2) (hG p)
    (fun n => schwartz_hasWeakPartial (f n p.2) p.1)

theorem derivative_limits_energy {f : ℕ → SchwartzField}
    {C : L2Vector} {D : L2Scalar} {G : DerivativeIndex → L2Scalar}
    (hC : ∀ j, Tendsto (fun n => curlL2 (f n) j) atTop (𝓝 (C j)))
    (hD : Tendsto (fun n => divL2 (f n)) atTop (𝓝 D))
    (hG : ∀ p, Tendsto (fun n => partialL2 (f n) p) atTop (𝓝 (G p))) :
    (∑ p, ‖G p‖ ^ 2) = (∑ j, ‖C j‖ ^ 2) + ‖D‖ ^ 2 := by
  have hl : Tendsto (fun n => ∑ p, ‖partialL2 (f n) p‖ ^ 2)
      atTop (𝓝 (∑ p, ‖G p‖ ^ 2)) :=
    tendsto_finset_sum _ (fun p _ => (hG p).norm.pow 2)
  have hr : Tendsto (fun n => (∑ j, ‖curlL2 (f n) j‖ ^ 2) + ‖divL2 (f n)‖ ^ 2)
      atTop (𝓝 ((∑ j, ‖C j‖ ^ 2) + ‖D‖ ^ 2)) :=
    (tendsto_finset_sum _ (fun j _ => (hC j).norm.pow 2)).add (hD.norm.pow 2)
  apply tendsto_nhds_unique hl
  exact hr.congr' (Eventually.of_forall (fun n => (schwartz_divcurl_energy (f n)).symm))

theorem weak_derivatives_of_approximation {E C : L2Vector} {D : L2Scalar}
    (f : ℕ → SchwartzField)
    (hE : ∀ j, Tendsto (fun n => FourierL2.embed (f n j)) atTop (𝓝 (E j)))
    (hC : ∀ j, Tendsto (fun n => curlL2 (f n) j) atTop (𝓝 (C j)))
    (hD : Tendsto (fun n => divL2 (f n)) atTop (𝓝 D)) :
    ∃ G : DerivativeIndex → L2Scalar,
      (∀ p, HasWeakPartial (E p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) = (∑ j, ‖C j‖ ^ 2) + ‖D‖ ^ 2 := by
  obtain ⟨G, hG⟩ := exists_derivative_limits hC hD
  refine ⟨G, fun p => ?_, derivative_limits_energy hC hD hG⟩
  exact weakPartial_limit p.1 (hE p.2) (hG p)
    (fun n => schwartz_hasWeakPartial (f n p.2) p.1)

/-- The full compact-support div–curl regularity statement, including exact
energy equality for the nine constructed genuine weak L2 derivatives. -/
theorem compact_weak_derivatives_energy {E C : L2Vector} {D : L2Scalar}
    (hE : ∀ j, CompactRepresentative (E j))
    (hC : HasWeakCurl E C) (hD : HasWeakDivergence E D) :
    ∃ G : DerivativeIndex → L2Scalar,
      (∀ p, HasWeakPartial (E p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) = (∑ j, ‖C j‖ ^ 2) + ‖D‖ ^ 2 := by
  obtain ⟨f, hf, hc, hd⟩ := compact_schwartz_graph_approximation hE hC hD
  exact weak_derivatives_of_approximation f hf hc hd

end OQ14.DivCurlRegularity

#print axioms OQ14.DivCurlRegularity.partialL2_norm_le
#print axioms OQ14.DivCurlRegularity.partialL2_dist_le
#print axioms OQ14.DivCurlRegularity.partialL2_cauchy
#print axioms OQ14.DivCurlRegularity.exists_derivative_limits
#print axioms OQ14.DivCurlRegularity.compact_weak_derivatives
#print axioms OQ14.DivCurlRegularity.derivative_limits_energy
#print axioms OQ14.DivCurlRegularity.weak_derivatives_of_approximation
#print axioms OQ14.DivCurlRegularity.compact_weak_derivatives_energy
