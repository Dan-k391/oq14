import Mathlib.GroupTheory.CosetCover
import FiniteMixedScaledFlux

/-! A finite family of nonzero linear response functionals has one common nonzero input. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.CommonInputAvoidance
open Set
variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℂ V]

theorem exists_simultaneous (L : ι → V →ₗ[ℂ] ℂ) (hne : ∀ i, L i ≠ 0) :
    ∃ v : V, ∀ i, L i v ≠ 0 := by
  classical
  let s : Finset (Submodule ℂ V) := Finset.univ.image (fun i => LinearMap.ker (L i))
  have hs : ⊤ ∉ s := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    have htop : LinearMap.ker (L i) = ⊤ := hi
    exact hne i (LinearMap.ker_eq_top.mp htop)
  have hcov := Subspace.biUnion_ne_univ_of_top_nmem hs
  have hex : ∃ v : V, v ∉ ⋃ q ∈ s, (q : Set V) := by
    by_contra hn
    apply hcov
    apply Set.eq_univ_iff_forall.mpr
    intro v
    by_contra hv
    exact hn ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, fun i hi => ?_⟩
  apply hv
  apply Set.mem_iUnion.mpr
  refine ⟨LinearMap.ker (L i), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · exact LinearMap.mem_ker.mpr hi

theorem exists_normalized [Nonempty ι] (k : ℝ) (hk : 0 < k)
    (L : ι → (ComplexTransverseExpansion.ModeIndex →₀ ℂ) →ₗ[ℂ] ℂ)
    (hne : ∀ i, L i ≠ 0) :
    ∃ v : ComplexTransverseExpansion.ModeIndex →₀ ℂ, v ≠ 0 ∧
      Filter.Tendsto (FiniteMixedScaledFlux.inwardPowerK k v) Filter.atTop (nhds 1) ∧
      ∀ i, L i v ≠ 0 := by
  obtain ⟨v, hv⟩ := exists_simultaneous L hne
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hv0 : v ≠ 0 := by
    intro h
    exact hv i (by simp [h])
  let z : ℂ := (k : ℂ) * (((Real.sqrt (FiniteMixedScaledFlux.E v))⁻¹ : ℝ) : ℂ)
  have hz : FiniteMixedScaledFlux.normalizeK k v = z • v := by
    unfold FiniteMixedScaledFlux.normalizeK FiniteMixedScaledFlux.normalize
    rw [smul_smul]
  have hnorm := FiniteMixedScaledFlux.normalizeK_ne_zero k hk v hv0
  have hz0 : z ≠ 0 := by
    intro h
    apply hnorm
    rw [hz, h, zero_smul]
  refine ⟨FiniteMixedScaledFlux.normalizeK k v, hnorm,
    FiniteMixedScaledFlux.normalizedK_limit k hk v hv0, ?_⟩
  intro j
  rw [hz, map_smul]
  exact mul_ne_zero hz0 (hv j)

end OQ14.CommonInputAvoidance
#print axioms OQ14.CommonInputAvoidance.exists_simultaneous
#print axioms OQ14.CommonInputAvoidance.exists_normalized
