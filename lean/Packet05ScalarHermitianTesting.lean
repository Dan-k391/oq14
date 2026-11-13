import Packet05ScalarH1Testing
import WeakPoynting.Poynting

/-! Hermitian testing of weak scalar divergence equations with actual compact
H¹ fields; complex conjugation preserves weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarHermitianTesting
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.WeakPower
  OQ14.Packet05ScalarH1Testing
open scoped ComplexConjugate

theorem conjugate_weak_partial (u v : L2Scalar) (i : Fin 3)
    (h : HasWeakPartial u v i) : HasWeakPartial (conjScalar u) (conjScalar v) i := by
  intro φ
  rw [valuePair_conj, derivativePair_conj, ← map_add, h (conjTest φ), map_zero]

theorem conjugate_compact (u : L2Scalar) (hu : CompactRepresentative u) :
    CompactRepresentative (conjScalar u) := by
  obtain ⟨f, hf, he⟩ := hu
  refine ⟨fun x => conj (f x), ?_, ?_⟩
  · exact hf.comp_left (by simp)
  · filter_upwards [conjScalar_ae u, he] with x hc hx
    rw [hc, hx]

theorem weak_divergence_test_compact_h1_conj (E : L2Vector) (D u : L2Scalar)
    (G : Fin 3 → L2Scalar) (hdiv : HasWeakDivergence E D)
    (hu : CompactRepresentative u) (hG : ∀ i, HasWeakPartial u (G i) i) :
    scalarProduct D (conjScalar u) + scalarProduct (E 0) (conjScalar (G 0)) +
      scalarProduct (E 1) (conjScalar (G 1)) + scalarProduct (E 2) (conjScalar (G 2)) = 0 :=
  weak_divergence_test_compact_h1 E D (conjScalar u) (fun i => conjScalar (G i)) hdiv
    (conjugate_compact u hu) (fun i => conjugate_weak_partial u (G i) i (hG i))

end OQ14.Packet05ScalarHermitianTesting
#print axioms OQ14.Packet05ScalarHermitianTesting.conjugate_weak_partial
#print axioms OQ14.Packet05ScalarHermitianTesting.conjugate_compact
#print axioms OQ14.Packet05ScalarHermitianTesting.weak_divergence_test_compact_h1_conj
