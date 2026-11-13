import Packet05QuantitativeGraphPiola
import Packet05QuantitativeBinaryForcing

/-! Fixed-chart uniform ceilings for the actual binary graph forcing. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05UniformGraphForcing
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphH2Pullback
  OQ14.Packet05GraphPullback OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphWeakDivergence
  OQ14.Packet05QuantitativeGraphPiola OQ14.Packet05QuantitativeBinaryForcing
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_binary_forcing_uniform (g : Plane → ℝ) (hg3 : ContDiff ℝ 3 g)
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
    (hL2 : ∀ i j k x, ‖dcoord (fun y => dcoord (slopeC g i) y j) x k‖ ≤ L2)
    (d : ℝ) (hd : 0 ≤ d) :
    let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
    let P := transformedFlux g hg Q (fun _ => B) hB
    let F : L2Vector := fun j => -OQ14.Packet05FlatWeight.mulWeight d hd (P j)
    ∃ F1 : Fin 3 → L2Vector, ∃ F2 : Fin 3 → Fin 3 → L2Vector,
      (∀ j, CompactRepresentative (F j)) ∧
      (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t) ∧
      (∑ j : Fin 3, ‖F j‖) ≤ 3*(1+d)*(1+3*B)*N ∧
      (∀ i, (∑ j : Fin 3, ‖F1 i j‖) ≤ 3*(1+d)*((1+B)+3*(B*(1+B)+L1))*N) ∧
      (∀ i t, (∑ j : Fin 3, ‖F2 i t j‖) ≤ 3*(1+d)*(((1+B)^2+L1)+3*(B*((1+B)^2+L1)+2*L1*(1+B)+L2))*N) := by
  dsimp only
  let hg : ContDiff ℝ 2 g := hg3.of_le (by decide)
  let P := transformedFlux g hg Q (fun _ => B) hB
  obtain ⟨PG,PH,hPc,hPG,hPH,hPnorm,hPGnorm,hPHnorm⟩ :=
    graph_piola_h2_uniform g hg3 Q QG QH hQc hG hH N B L1 L2 hN hNG hNH hB hdi hdd hL1 hL2
  have hforce := binary_forcing_arrays d hd P PG PH hPc hPG hPH
  dsimp only at hforce
  let F : L2Vector := fun j => -OQ14.Packet05FlatWeight.mulWeight d hd (P j)
  let F1 : Fin 3 → L2Vector := fun i j => -OQ14.Packet05FlatWeight.mulWeight d hd (PG i j)
  let F2 : Fin 3 → Fin 3 → L2Vector := fun i t j => -OQ14.Packet05FlatWeight.mulWeight d hd (PH i t j)
  change (∀ j, CompactRepresentative (F j)) ∧
    (∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i) ∧
    (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t) ∧
    (∀ j, ‖F j‖ ≤ (1+d)*‖P j‖) ∧
    (∀ i j, ‖F1 i j‖ ≤ (1+d)*‖PG i j‖) ∧
    (∀ i t j, ‖F2 i t j‖ ≤ (1+d)*‖PH i t j‖) at hforce
  obtain ⟨hf,hf1,hf2,hfn,hf1n,hf2n⟩ := hforce
  have hd0 : 0 ≤ 1+d := by linarith
  refine ⟨F1,F2,hf,hf1,hf2,?_,?_,?_⟩
  · have h0 := (hfn 0).trans (mul_le_mul_of_nonneg_left (hPnorm 0) hd0)
    have h1 := (hfn 1).trans (mul_le_mul_of_nonneg_left (hPnorm 1) hd0)
    have h2 := (hfn 2).trans (mul_le_mul_of_nonneg_left (hPnorm 2) hd0)
    simp only [Fin.sum_univ_three]
    linarith
  · intro i
    have h0 := (hf1n i 0).trans (mul_le_mul_of_nonneg_left (hPGnorm i 0) hd0)
    have h1 := (hf1n i 1).trans (mul_le_mul_of_nonneg_left (hPGnorm i 1) hd0)
    have h2 := (hf1n i 2).trans (mul_le_mul_of_nonneg_left (hPGnorm i 2) hd0)
    simp only [Fin.sum_univ_three]
    linarith
  · intro i t
    have h0 := (hf2n i t 0).trans (mul_le_mul_of_nonneg_left (hPHnorm i t 0) hd0)
    have h1 := (hf2n i t 1).trans (mul_le_mul_of_nonneg_left (hPHnorm i t 1) hd0)
    have h2 := (hf2n i t 2).trans (mul_le_mul_of_nonneg_left (hPHnorm i t 2) hd0)
    simp only [Fin.sum_univ_three]
    linarith

end OQ14.Packet05UniformGraphForcing
#print axioms OQ14.Packet05UniformGraphForcing.graph_binary_forcing_uniform
