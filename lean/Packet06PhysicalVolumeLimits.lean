import Packet05ActualMaximum
import Mathlib.Topology.Algebra.Order.Field

/-! Reciprocal physical energy and fixed-direction complex volume limits
from a diverging Euclidean electric amplitude. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06PhysicalVolumeLimits
open Filter
open scoped Topology

def amplitude (e : Fin 3 → ℂ) : ℝ := Real.sqrt (∑ k : Fin 3, ‖e k‖^2)

theorem weighted_inverse_square (f ε : ℕ → ℝ)
    (hf : Tendsto f atTop atTop) (hε : ∀ j, 1 ≤ ε j) :
    Tendsto (fun j => 1/(ε j*(f j)^2)) atTop (𝓝 0) := by
  have hden : Tendsto (fun j => ε j*(f j)^2) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hf
    filter_upwards [hf.eventually_ge_atTop 1] with j hj
    have he := mul_le_mul_of_nonneg_right (hε j) (sq_nonneg (f j))
    nlinarith
  simpa only [one_div] using tendsto_inv_atTop_zero.comp hden

theorem fixed_direction_subsequence (E : ℕ → Fin 3 → ℂ)
    (hE : Tendsto (fun j => amplitude (E j)) atTop atTop) :
    ∃ (i : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun j => ‖E (φ j) i‖) atTop atTop := by
  classical
  have hmax (j : ℕ) : ∃ i : Fin 3, ∀ k : Fin 3, ‖E j k‖ ≤ ‖E j i‖ := by
    obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ (fun k : Fin 3 => ‖E j k‖)
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty)
    exact ⟨i,fun k => hi k (Finset.mem_univ k)⟩
  choose idx hidx using hmax
  have hbound (j : ℕ) : amplitude (E j) ≤ 3*‖E j (idx j)‖ := by
    have hs : 0 ≤ ∑ k : Fin 3, ‖E j k‖^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have ha : (amplitude (E j))^2=∑ k : Fin 3, ‖E j k‖^2 := Real.sq_sqrt hs
    have hsq (k : Fin 3) : ‖E j k‖^2 ≤ ‖E j (idx j)‖^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hidx j k) 2
    have hsum : (∑ k : Fin 3, ‖E j k‖^2) ≤ 3*‖E j (idx j)‖^2 := by
      simpa using Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) => hsq k)
    have hnon : 0 ≤ amplitude (E j) := Real.sqrt_nonneg _
    nlinarith [norm_nonneg (E j (idx j))]
  have hfreq : ∃ i : Fin 3, ∃ᶠ j : ℕ in atTop, idx j=i := by
    by_contra hn
    have hnot : ∀ i : Fin 3, ∀ᶠ j : ℕ in atTop, idx j ≠ i := by
      intro i
      exact not_frequently.mp (fun hi => hn ⟨i,hi⟩)
    obtain ⟨j,hj⟩ := (Filter.eventually_all.mpr hnot).exists
    exact hj (idx j) rfl
  obtain ⟨i,hi⟩ := hfreq
  obtain ⟨φ,hφ,hφi⟩ := extraction_of_frequently_atTop hi
  refine ⟨i,φ,hφ,?_⟩
  have hsub := hE.comp hφ.tendsto_atTop
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hsub.eventually_ge_atTop (3*b)] with j hj
  have hb := hbound (φ j)
  rw [hφi j] at hb
  dsimp only [Function.comp_def] at hj
  linarith

theorem physical_and_directional_volumes (E : ℕ → Fin 3 → ℂ) (ε : ℕ → ℝ)
    (hE : Tendsto (fun j => amplitude (E j)) atTop atTop) (hε : ∀ j, 1 ≤ ε j) :
    Tendsto (fun j => 1/(ε j*(amplitude (E j))^2)) atTop (𝓝 0) ∧
      ∃ (i : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ᶠ j in atTop, E (φ j) i ≠ 0) ∧
        Tendsto (fun j => (((ε (φ j) : ℝ) : ℂ)*(E (φ j) i)^2)⁻¹) atTop (𝓝 0) := by
  refine ⟨weighted_inverse_square _ _ hE hε,?_⟩
  obtain ⟨i,φ,hφ,hcomp⟩ := fixed_direction_subsequence E hE
  refine ⟨i,φ,hφ,?_,?_⟩
  · filter_upwards [hcomp.eventually_gt_atTop 0] with j hj
    exact norm_pos_iff.mp hj
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hh := weighted_inverse_square (fun j => ‖E (φ j) i‖) (fun j => ε (φ j)) hcomp (fun j => hε (φ j))
    have habs (j : ℕ) : |ε (φ j)|=ε (φ j) := abs_of_nonneg (le_trans zero_le_one (hε (φ j)))
    simpa only [norm_inv,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      habs,one_div] using hh

end OQ14.Packet06PhysicalVolumeLimits
#print axioms OQ14.Packet06PhysicalVolumeLimits.weighted_inverse_square
#print axioms OQ14.Packet06PhysicalVolumeLimits.fixed_direction_subsequence
#print axioms OQ14.Packet06PhysicalVolumeLimits.physical_and_directional_volumes
