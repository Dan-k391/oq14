import Packet05MultiplierH2Norm
import Packet05GraphPiolaCompact
import Packet05QuantitativeBinaryForcing

/-! Quantitative H² bounds for the actual Piola-transformed correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet05QuantitativeGraphPiola
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphH2Pullback
  OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeakDivergence
  OQ14.Packet05GraphH2Norm OQ14.Packet05MultiplierH2Norm OQ14.Packet05GraphPiolaH2
  OQ14.Packet05GraphPiolaCompact OQ14.Packet05BoundedWeakMultiplier
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_piola_h2_uniform (g : Plane → ℝ) (hg3 : ContDiff ℝ 3 g)
    (Q : L2Vector) (QG : Fin 3 → L2Vector) (QH : Fin 3 → Fin 3 → L2Vector)
    (hQc : ∀ j, CompactRepresentative (Q j))
    (hG : ∀ j i, HasWeakPartial (Q j) (QG j i) i)
    (hH : ∀ j i t, HasWeakPartial (QG j i) (QH j i t) t)
    (N B L1 L2 : ℝ) (hN : ∀ j, ‖Q j‖ ≤ N)
    (hNG : ∀ j i, ‖QG j i‖ ≤ N) (hNH : ∀ j i t, ‖QH j i t‖ ≤ N)
    (hB : ∀ i x, ‖slopeC g i x‖ ≤ B)
    (hdi : ∀ i j, MemLp (fun x => dcoord (slopeC g i) x j) ⊤ volume)
    (hdd : ∀ i j k, MemLp (fun x => dcoord (fun y => dcoord (slopeC g i) y j) x k) ⊤ volume)
    (hL1 : ∀ i j x, ‖dcoord (slopeC g i) x j‖ ≤ L1)
    (hL2 : ∀ i j k x, ‖dcoord (fun y => dcoord (slopeC g i) y j) x k‖ ≤ L2) :
    let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
    let P := transformedFlux g hg Q (fun _ => B) hB
    ∃ PG : Fin 3 → L2Vector, ∃ PH : Fin 3 → Fin 3 → L2Vector,
      (∀ j, CompactRepresentative (P j)) ∧
      (∀ i j, HasWeakPartial (P j) (PG i j) i) ∧
      (∀ i t j, HasWeakPartial (PG i j) (PH i t j) t) ∧
      (∀ j, ‖P j‖ ≤ (1+3*B)*N) ∧
      (∀ i j, ‖PG i j‖ ≤ ((1+B)+3*(B*(1+B)+L1))*N) ∧
      (∀ i t j, ‖PH i t j‖ ≤ (((1+B)^2+L1)+3*(B*((1+B)^2+L1)+2*L1*(1+B)+L2))*N) := by
  dsimp only
  let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
  let Bs : Fin 3 → ℝ := fun _ => B
  let Ls : Fin 3 → Fin 3 → ℝ := fun _ _ => L1
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
  have hL10 : 0 ≤ L1 := (norm_nonneg _).trans (hL1 0 0 0)
  have hL20 : 0 ≤ L2 := (norm_nonneg _).trans (hL2 0 0 0 0)
  let V (j : Fin 3) := pullback g hg.continuous (Q j)
  let VG (j i : Fin 3) := pulledGradient g hg (QG j) Bs hB i
  have hp (j : Fin 3) := graph_pullback_h2_bounded g hg (Q j) (QG j) (QH j) (hG j) (hH j) Bs hB hdi Ls hL1
  choose VH hVG hVH hVHnorm using hp
  have hV (j : Fin 3) : ‖V j‖ ≤ N := by simpa [V,pullback_norm] using hN j
  have hVGnorm (j i : Fin 3) : ‖VG j i‖ ≤ (1+B)*N := by
    have h := pulled_gradient_norm g hg (QG j) Bs hB i
    dsimp [VG,Bs] at h
    have hm := mul_le_mul_of_nonneg_left (hNG j 2) hB0
    nlinarith [hNG j i]
  have hVHn (j i t : Fin 3) : ‖VH j i t‖ ≤ ((1+B)^2+L1)*N := by
    have h := hVHnorm j i t
    dsimp [Bs,Ls] at h
    have h0 := hNH j i t; have h1 := hNH j i 2; have h2 := hNH j 2 t; have h3 := hNH j 2 2
    have h4 := hNG j 2
    have hB2 : 0 ≤ B^2 := sq_nonneg B
    nlinarith [mul_le_mul_of_nonneg_left h1 hB0, mul_le_mul_of_nonneg_left h2 hB0,
      mul_le_mul_of_nonneg_left h3 hB2, mul_le_mul_of_nonneg_left h4 hL10]
  let M (j : Fin 3) := slopeMul g hg j B (hB j) (V j)
  have hm (j : Fin 3) := bounded_multiplier_h2_norm (slopeC g j) (slopeC_contDiff2 g hg3 j)
    (slopeC_memLp_top g hg j B (hB j)) (hdi j) (hdd j) B L1 L2 (hB j) (hL1 j) (hL2 j)
    (V j) (VG j) (VH j) (hVG j) (hVH j)
  choose MG MH hMG hMH hMGnorm hMHnorm using hm
  have hM (j : Fin 3) : ‖M j‖ ≤ B*N := by
    have h := slope_multiply_norm g hg j B (hB j) (V j)
    have hh := mul_le_mul_of_nonneg_left (hV j) hB0
    exact h.trans hh
  have hMGn (j i : Fin 3) : ‖MG j i‖ ≤ (B*(1+B)+L1)*N := by
    have h := hMGnorm j i
    have h0 := hVGnorm j i; have h1 := hV j
    nlinarith [mul_le_mul_of_nonneg_left h0 hB0, mul_le_mul_of_nonneg_left h1 hL10]
  have hMHn (j i t : Fin 3) : ‖MH j i t‖ ≤ (B*((1+B)^2+L1)+2*L1*(1+B)+L2)*N := by
    have h := hMHnorm j i t
    have h0 := hVHn j i t; have h1 := hVGnorm j i; have h2 := hVGnorm j t; have h3 := hV j
    nlinarith [mul_le_mul_of_nonneg_left h0 hB0, mul_le_mul_of_nonneg_left h1 hL10,
      mul_le_mul_of_nonneg_left h2 hL10, mul_le_mul_of_nonneg_left h3 hL20]
  let PG (i j : Fin 3) : L2Scalar := if j = 2 then VG 2 i - MG 0 i - MG 1 i - MG 2 i else VG j i
  let PH (i t j : Fin 3) : L2Scalar := if j = 2 then VH 2 i t - MH 0 i t - MH 1 i t - MH 2 i t else VH j i t
  have hM0 : ∀ i j, HasWeakPartial (M j) (MG j i) i := by
    intro i j
    exact hMG j i
  have hM1 : ∀ i t j, HasWeakPartial (MG j i) (MH j i t) t := by
    intro i t j
    exact hMH j i t
  refine ⟨PG,PH,graph_piola_compact g hg Q hQc Bs hB,?_,?_,?_,?_,?_⟩
  · intro i j
    by_cases hj : j=2
    · subst j
      simp only [transformedFlux, ↓reduceIte, PG]
      exact weak_partial_sub _ _ _ _ i (weak_partial_sub _ _ _ _ i
        (weak_partial_sub _ _ _ _ i (hVG 2 i) (hM0 i 0)) (hM0 i 1)) (hM0 i 2)
    · simpa only [transformedFlux,hj,↓reduceIte,PG] using hVG j i
  · intro i t j
    by_cases hj : j=2
    · subst j
      simp only [PG,PH, ↓reduceIte]
      exact weak_partial_sub _ _ _ _ t (weak_partial_sub _ _ _ _ t
        (weak_partial_sub _ _ _ _ t (hVH 2 i t) (hM1 i t 0)) (hM1 i t 1)) (hM1 i t 2)
    · simpa only [PG,PH,hj,↓reduceIte] using hVH j i t
  · intro j
    by_cases hj : j=2
    · subst j
      simp only [transformedFlux, ↓reduceIte]
      have h0 := hV 2; have h1 := hM 0; have h2 := hM 1; have h3 := hM 2
      have n1 := norm_sub_le (V 2) (M 0)
      have n2 := norm_sub_le (V 2-M 0) (M 1)
      have n3 := norm_sub_le (V 2-M 0-M 1) (M 2)
      nlinarith
    · simp only [transformedFlux,hj,↓reduceIte]
      have h := hV j
      nlinarith [mul_nonneg hB0 hN0]
  · intro i j
    by_cases hj : j=2
    · subst j
      simp only [PG,↓reduceIte]
      have h0 := hVGnorm 2 i; have h1 := hMGn 0 i; have h2 := hMGn 1 i; have h3 := hMGn 2 i
      have n1 := norm_sub_le (VG 2 i) (MG 0 i)
      have n2 := norm_sub_le (VG 2 i-MG 0 i) (MG 1 i)
      have n3 := norm_sub_le (VG 2 i-MG 0 i-MG 1 i) (MG 2 i)
      nlinarith
    · simp only [PG,hj,↓reduceIte]
      have h := hVGnorm j i
      have hp : 0 ≤ (B*(1+B)+L1)*N := by positivity
      nlinarith
  · intro i t j
    by_cases hj : j=2
    · subst j
      simp only [PH,↓reduceIte]
      have h0 := hVHn 2 i t; have h1 := hMHn 0 i t; have h2 := hMHn 1 i t; have h3 := hMHn 2 i t
      have n1 := norm_sub_le (VH 2 i t) (MH 0 i t)
      have n2 := norm_sub_le (VH 2 i t-MH 0 i t) (MH 1 i t)
      have n3 := norm_sub_le (VH 2 i t-MH 0 i t-MH 1 i t) (MH 2 i t)
      nlinarith
    · simp only [PH,hj,↓reduceIte]
      have h := hVHn j i t
      have hp : 0 ≤ (B*((1+B)^2+L1)+2*L1*(1+B)+L2)*N := by positivity
      nlinarith

end OQ14.Packet05QuantitativeGraphPiola
#print axioms OQ14.Packet05QuantitativeGraphPiola.graph_piola_h2_uniform
