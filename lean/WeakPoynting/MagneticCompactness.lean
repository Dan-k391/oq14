import WeakPoynting.Compactness
import WeakPoynting.RegularityBounds

/-! # Interior compactness of actual weak Maxwell magnetic fields -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MagneticCompactness

open MeasureTheory OQ14.Maxwell OQ14.CurlCutoff OQ14.LocalRegularity
  OQ14.DivCurlCompact OQ14.DivCurlRegularity OQ14.RegularityBounds
  OQ14.WeakCompactness Filter
open scoped Topology

theorem cutoff_bounds (χ : WeakCurl.Test) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ x, ‖χ.function x‖ ≤ A) ∧ (∀ i x, ‖dcoord χ.function x i‖ ≤ B) := by
  obtain ⟨A, hA⟩ := χ.compact.exists_bound_of_continuous χ.regular.continuous
  have hb (i : Fin 3) : ∃ B : ℝ, ∀ x, ‖dcoord χ.function x i‖ ≤ B :=
    (χ.compact.fderiv_apply ℝ (basis i)).exists_bound_of_continuous
      (partial_continuous χ.regular i)
  choose B hB using hb
  refine ⟨max A 0, ∑ i : Fin 3, |B i|, le_max_right _ _, by positivity,
    fun x => (hA x).trans (le_max_left _ _), ?_⟩
  intro i x
  exact (hB i x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_univ i)))

theorem cutoff_extend_supported {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (E : DomainCurl.L2Vector Ω) {R : ℝ}
    (hR : tsupport χ.function ⊆ Metric.closedBall 0 R) (j : Fin 3) :
    SupportedIn (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest E) j)
      (Metric.closedBall 0 R) := by
  have hm := (ae_restrict_iff' hΩ.measurableSet).mp
    (mulL2_ae Ω χ.function χ.regular.continuous χ.compact (E j))
  filter_upwards [extendScalar_ae Ω hΩ.measurableSet (multiply Ω χ.toTest E j), hm]
    with x he hx
  intro hn
  have hz : χ.function x = 0 :=
    image_eq_zero_of_nmem_tsupport (fun ht => hn (hR ht))
  change extendScalar Ω hΩ.measurableSet (multiply Ω χ.toTest E j) x = 0
  rw [he]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ]
    change mulL2 Ω χ.function χ.regular.continuous χ.compact (E j) x = 0
    rw [hx hxΩ, hz, zero_mul]
  · exact Set.indicator_of_not_mem hxΩ _

theorem derivative_coordinate_sum_bound {G : DerivativeIndex → WeakCurl.L2Scalar}
    {Q : ℝ} (hQ : (∑ p, ‖G p‖ ^ 2) ≤ Q) (j : Fin 3) :
    (∑ i : Fin 3, ‖G (i, j)‖) ≤ 3 * (Q + 1) := by
  have hb (i : Fin 3) : ‖G (i, j)‖ ≤ Q + 1 := by
    have hs : ‖G (i, j)‖ ^ 2 ≤ ∑ p, ‖G p‖ ^ 2 :=
      Finset.single_le_sum (fun p _ => sq_nonneg ‖G p‖) (Finset.mem_univ (i, j))
    nlinarith [sq_nonneg (‖G (i, j)‖ - 1 / 2)]
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_ofNat] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hb i)

/-- Bounded actual regional Maxwell solutions have precompact interior magnetic
cutoffs in the whole-space L2 norm. No derivative or separate regularity
premise on the scalar permittivity is required. -/
theorem maxwell_cutoff_precompact {ι : Type*} {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M)
    (E H : ι → DomainCurl.HCurl Ω)
    (hMax : ∀ t, WeakConservation.WeakMaxwell ω (fun _ => 1) ε (E t) (H t))
    (hE : ∀ t, ‖(E t).val.1‖ ≤ L) (hH : ∀ t, ‖(H t).val.1‖ ≤ L) :
    IsCompact (closure (Set.range (fun t =>
      extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest (H t).val.1)))) := by
  obtain ⟨A, B, hA, hB, hvχ, hdχ⟩ := cutoff_bounds χ.toTest
  obtain ⟨R, hR⟩ := χ.compact.isBounded.subset_closedBall (0 : Space)
  let Q := 3 * (A * (|ω| * M * L) + 2 * B * L)^2 + (3 * B * L)^2
  let S := closure (weakH1Ball R (A * L) (3 * (Q + 1)))
  have hS : IsCompact S := weakH1Ball_compactClosure R (A * L) _ (mul_nonneg hA hL)
  have hp : IsCompact {F : WeakCurl.L2Vector | ∀ j, F j ∈ S} :=
    isCompact_pi_infinite (fun _ : Fin 3 => hS)
  apply hp.of_isClosed_subset isClosed_closure
  apply closure_minimal
  · rintro F ⟨t, rfl⟩
    obtain ⟨G, hG, henergy⟩ := maxwell_cutoff_h1_bound hΩ χ hχ hA hB hM
      hvχ hdχ ω hω ε (E t) (H t) (hMax t) hε
    have he : (∑ p, ‖G p‖ ^ 2) ≤ Q := by
      have h1 : A * (|ω| * M * ‖(E t).val.1‖) + 2 * B * ‖(H t).val.1‖ ≤
          A * (|ω| * M * L) + 2 * B * L :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hE t) (mul_nonneg (abs_nonneg _) hM)) hA)
          (mul_le_mul_of_nonneg_left (hH t) (by positivity))
      have h2 : 3 * B * ‖(H t).val.1‖ ≤ 3 * B * L :=
        mul_le_mul_of_nonneg_left (hH t) (by positivity)
      have hs1 := pow_le_pow_left₀
        (by positivity : 0 ≤ A * (|ω| * M * ‖(E t).val.1‖) + 2 * B * ‖(H t).val.1‖) h1 2
      have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ 3 * B * ‖(H t).val.1‖) h2 2
      dsimp [Q]
      linarith
    intro j
    apply subset_closure
    refine ⟨?_, cutoff_extend_supported hΩ χ (H t).val.1 hR j,
      fun i => G (i, j), fun i => hG (i, j), derivative_coordinate_sum_bound he j⟩
    change ‖extendScalar Ω hΩ.measurableSet (multiply Ω χ.toTest (H t).val.1 j)‖ ≤ A * L
    rw [extendScalar_norm]
    exact ((norm_le_pi_norm (multiply Ω χ.toTest (H t).val.1) j).trans
      (multiply_norm_le Ω χ.toTest (H t).val.1 hA hvχ)).trans
      (mul_le_mul_of_nonneg_left (hH t) hA)
  · exact hp.isClosed

/-- One cutoff works for the entire family and equals one on a common open
neighborhood of the prescribed compact interior set. -/
theorem maxwell_magnetic_local_precompact {ι : Type*} {Ω K : Set Space}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M)
    (E H : ι → DomainCurl.HCurl Ω)
    (hMax : ∀ t, WeakConservation.WeakMaxwell ω (fun _ => 1) ε (E t) (H t))
    (hE : ∀ t, ‖(E t).val.1‖ ≤ L) (hH : ∀ t, ‖(H t).val.1‖ ≤ L) :
    ∃ (U : Set Space) (F : ι → WeakCurl.L2Vector),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧ IsCompact (closure (Set.range F)) ∧
      ∀ t j, (fun x => F t j x) =ᵐ[volume.restrict U] (fun x => (H t).val.1 j x) := by
  obtain ⟨χ, hχ, hχK⟩ := exists_c2_interior_cutoff hΩ hK hKΩ
  let U := interior {x | χ.function x = 1} ∩ Ω
  have hU : IsOpen U := isOpen_interior.inter hΩ
  have hUΩ : U ⊆ Ω := Set.inter_subset_right
  have hKU : K ⊆ U := by
    intro x hx
    exact ⟨mem_interior_iff_mem_nhds.mpr (hχK x hx), hKΩ hx⟩
  refine ⟨U, fun t => extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest (H t).val.1),
    hU, hKU, hUΩ, maxwell_cutoff_precompact hΩ χ hχ ω hω ε hM hL hε E H hMax hE hH, ?_⟩
  intro t j
  have hh := (ae_restrict_iff' hΩ.measurableSet).mp
    (LocalPower.cutExtend_field_ae hΩ χ (H t) j)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hh] with x hx
  intro hxu
  have hχx : χ.function x = 1 :=
    (show interior {y | χ.function y = 1} ⊆ {y | χ.function y = 1}
      from interior_subset) hxu.1
  change (LocalPower.cutExtend hΩ χ (H t)).val.1 j x = (H t).val.1 j x
  rw [hx (hUΩ hxu), hχx, one_mul]

/-- Every bounded sequence of actual regional Maxwell fields has a magnetic
subsequence converging strongly in L2 on a neighborhood of each prescribed
compact interior set. Agreement with the original fields is explicitly a.e.;
the convergence is the actual whole-space L2 norm of the cutoff representatives. -/
theorem maxwell_magnetic_local_subsequence {Ω K : Set Space}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M)
    (E H : ℕ → DomainCurl.HCurl Ω)
    (hMax : ∀ n, WeakConservation.WeakMaxwell ω (fun _ => 1) ε (E n) (H n))
    (hE : ∀ n, ‖(E n).val.1‖ ≤ L) (hH : ∀ n, ‖(H n).val.1‖ ≤ L) :
    ∃ (U : Set Space) (F : ℕ → WeakCurl.L2Vector) (G : WeakCurl.L2Vector) (s : ℕ → ℕ),
      IsOpen U ∧ K ⊆ U ∧ U ⊆ Ω ∧
      (∀ n j, (fun x => F n j x) =ᵐ[volume.restrict U] (fun x => (H n).val.1 j x)) ∧
      StrictMono s ∧ Tendsto (F ∘ s) atTop (𝓝 G) := by
  obtain ⟨U, F, hU, hKU, hUΩ, hc, he⟩ :=
    maxwell_magnetic_local_precompact hΩ hK hKΩ ω hω ε hM hL hε E H hMax hE hH
  obtain ⟨G, _, s, hs, ht⟩ :=
    hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨U, F, G, s, hU, hKU, hUΩ, he, hs, ht⟩

end OQ14.MagneticCompactness

#print axioms OQ14.MagneticCompactness.cutoff_bounds
#print axioms OQ14.MagneticCompactness.cutoff_extend_supported
#print axioms OQ14.MagneticCompactness.derivative_coordinate_sum_bound
#print axioms OQ14.MagneticCompactness.maxwell_cutoff_precompact
#print axioms OQ14.MagneticCompactness.maxwell_magnetic_local_precompact
#print axioms OQ14.MagneticCompactness.maxwell_magnetic_local_subsequence
