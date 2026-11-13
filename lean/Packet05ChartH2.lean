import Packet05ChartWeakDivergence
import Packet05GraphPiolaH2
import Packet05ActualCorrectionH2

/-! The signed physical chart carries compact H² correction components to
compact H² chart components, including all transformed derivative signs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ChartH2
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv OQ14.Packet05ChartWeakGradient
  OQ14.Packet05ChartWeakDivergence OQ14.Packet05GraphPiolaH2 OQ14.Packet05ActualCorrectionH2

theorem chart_pull_compact (up : Bool) (i : Fin 3) (u : L2Scalar)
    (hu : CompactRepresentative u) : CompactRepresentative (chartPull up i u) := by
  obtain ⟨f,hf,hu⟩ := hu
  refine ⟨fun x => f (inverseOriented up i x), ?_, ?_⟩
  · exact hf.comp_homeomorph (orientedHomeomorph up i).symm
  · have ht := (oriented_inverse_measure_preserving up i).quasiMeasurePreserving.ae hu
    filter_upwards [chartPull_ae up i u,ht] with x h1 h2
    exact h1.trans h2

theorem chart_pull_h2 (up : Bool) (i : Fin 3) (u : L2Scalar) (hu : HasH2 u) :
    HasH2 (chartPull up i u) := by
  obtain ⟨G,H,hG,hH⟩ := hu
  let D : L2Vector := fun j => (chartSign up j : ℂ) • chartPull up i (G (Equiv.swap i 2 j))
  let K : Fin 3 → L2Vector := fun j k =>
    ((chartSign up j : ℂ) * (chartSign up k : ℂ)) •
      chartPull up i (H (Equiv.swap i 2 j) (Equiv.swap i 2 k))
  refine ⟨D,K,?_,?_⟩
  · intro j
    exact chart_weak_partial up i j u (G (Equiv.swap i 2 j)) (hG _)
  · intro j k
    have hh := chart_weak_partial up i k (G (Equiv.swap i 2 j))
      (H (Equiv.swap i 2 j) (Equiv.swap i 2 k)) (hH _ _)
    simpa only [D,K,smul_smul] using weak_partial_smul (chartSign up j : ℂ) _ _ k hh

theorem chart_vector_compact_h2 (up : Bool) (i : Fin 3) (P : L2Vector)
    (hcompact : ∀ j, CompactRepresentative (P j)) (h2 : ∀ j, HasH2 (P j)) :
    (∀ j, CompactRepresentative (chartVector up i P j)) ∧
      (∀ j, HasH2 (chartVector up i P j)) := by
  constructor
  · intro j
    obtain ⟨f,hf,hu⟩ := chart_pull_compact up i _ (hcompact (Equiv.swap i 2 j))
    refine ⟨fun x => (chartSign up j : ℂ)*f x, hf.mul_left, ?_⟩
    filter_upwards [Lp.coeFn_smul (chartSign up j : ℂ) (chartPull up i (P (Equiv.swap i 2 j))),hu] with x ha hb
    change ((chartSign up j : ℂ) • chartPull up i (P (Equiv.swap i 2 j))) x = _
    rw [ha]
    simp only [Pi.smul_apply,smul_eq_mul,hb]
  · intro j
    obtain ⟨G,H,hG,hH⟩ := chart_pull_h2 up i _ (h2 (Equiv.swap i 2 j))
    refine ⟨fun k => (chartSign up j : ℂ) • G k,
      fun k l => (chartSign up j : ℂ) • H k l, ?_, ?_⟩
    · intro k
      exact weak_partial_smul _ _ _ _ (hG k)
    · intro k l
      exact weak_partial_smul _ _ _ _ (hH k l)

end OQ14.Packet05ChartH2
#print axioms OQ14.Packet05ChartH2.chart_pull_compact
#print axioms OQ14.Packet05ChartH2.chart_pull_h2
#print axioms OQ14.Packet05ChartH2.chart_vector_compact_h2
