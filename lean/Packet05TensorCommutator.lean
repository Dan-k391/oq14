import MaxwellCurlCutoffSource

/-! L² difference quotients of smooth matrix-valued coefficients.  This is
the commutator needed after a non-affine interface-flattening map; it does
not assume that the transformed Maxwell system has already been proved. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05TensorCommutator
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCutoffCommutator

theorem quotient_add (u v : L2Scalar) (i : Fin 3) (h : ℝ) :
    quotient (u+v) i h = quotient u i h + quotient v i h := by
  apply Lp.ext
  have hshift := (measurePreserving_add_right (volume : Measure Space) (h • basis i)).quasiMeasurePreserving.ae
    (Lp.coeFn_add u v)
  filter_upwards [quotient_ae (u+v) i h, quotient_ae u i h, quotient_ae v i h,
    Lp.coeFn_add u v, hshift, Lp.coeFn_add (quotient u i h) (quotient v i h)] with x hab ha hb hs ht hq
  rw [hq]
  simp only [Pi.add_apply]
  rw [hab,ha,hb,hs,ht]
  simp only [Pi.add_apply]
  ring

def matrixField (A : Fin 3 → Fin 3 → Test) (C : L2Vector) : L2Vector := fun j =>
  scaleL2 (A j 0).function (A j 0).regular.continuous (A j 0).compact (C 0) +
  scaleL2 (A j 1).function (A j 1).regular.continuous (A j 1).compact (C 1) +
  scaleL2 (A j 2).function (A j 2).regular.continuous (A j 2).compact (C 2)

theorem matrixField_quotient_bound (A : Fin 3 → Fin 3 → Test) (C : L2Vector)
    (i j : Fin 3) (h : ℝ) (hh : h ≠ 0) (a b : ℝ)
    (ha : ∀ p q x, ‖(A p q).function x‖ ≤ a)
    (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    ‖quotient (matrixField A C j) i h‖ ≤
      a * (‖quotient (C 0) i h‖ + ‖quotient (C 1) i h‖ + ‖quotient (C 2) i h‖) +
      3*b * (‖C 0‖ + ‖C 1‖ + ‖C 2‖) := by
  have h0 := cutoff_quotient_norm (A j 0) (C 0) i h hh a b (ha j 0) (hb j 0)
  have h1 := cutoff_quotient_norm (A j 1) (C 1) i h hh a b (ha j 1) (hb j 1)
  have h2 := cutoff_quotient_norm (A j 2) (C 2) i h hh a b (ha j 2) (hb j 2)
  let X0 : L2Scalar := scaleL2 (A j 0).function (A j 0).regular.continuous (A j 0).compact (C 0)
  let X1 : L2Scalar := scaleL2 (A j 1).function (A j 1).regular.continuous (A j 1).compact (C 1)
  let X2 : L2Scalar := scaleL2 (A j 2).function (A j 2).regular.continuous (A j 2).compact (C 2)
  change ‖quotient (X0 + X1 + X2) i h‖ ≤ _
  rw [quotient_add, quotient_add]
  have hn : ‖quotient X0 i h + quotient X1 i h + quotient X2 i h‖ ≤
      ‖quotient X0 i h‖ + ‖quotient X1 i h‖ + ‖quotient X2 i h‖ :=
    (norm_add_le (_ + _) _).trans (add_le_add_right (norm_add_le _ _) _)
  linarith

end OQ14.Packet05TensorCommutator
#print axioms OQ14.Packet05TensorCommutator.quotient_add
#print axioms OQ14.Packet05TensorCommutator.matrixField_quotient_bound
