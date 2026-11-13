import Packet05ChartH2

/-! The signed chart preserves componentwise uniform H² norm ceilings. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ChartH2Uniform
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv OQ14.Packet05ChartWeakGradient
  OQ14.Packet05ChartWeakDivergence OQ14.Packet05ChartH2 OQ14.Packet05ActualCorrectionH2

theorem chart_pull_norm (up : Bool) (i : Fin 3) (u : L2Scalar) : ‖chartPull up i u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (oriented_inverse_measure_preserving up i)

theorem chart_sign_norm (up : Bool) (i : Fin 3) : ‖(chartSign up i : ℂ)‖ = 1 := by
  unfold chartSign
  split_ifs <;> norm_num

theorem chart_vector_h2_uniform (up : Bool) (axis : Fin 3) (P : L2Vector)
    (G : Fin 3 → L2Vector) (H : Fin 3 → Fin 3 → L2Vector)
    (hPc : ∀ j, CompactRepresentative (P j))
    (hG : ∀ j i, HasWeakPartial (P j) (G j i) i)
    (hH : ∀ j i t, HasWeakPartial (G j i) (H j i t) t)
    (N : ℝ) (hP : ∀ j, ‖P j‖ ≤ N) (hGn : ∀ j i, ‖G j i‖ ≤ N)
    (hHn : ∀ j i t, ‖H j i t‖ ≤ N) :
    ∃ QG : Fin 3 → L2Vector, ∃ QH : Fin 3 → Fin 3 → L2Vector,
      (∀ j, CompactRepresentative (chartVector up axis P j)) ∧
      (∀ j i, HasWeakPartial (chartVector up axis P j) (QG j i) i) ∧
      (∀ j i t, HasWeakPartial (QG j i) (QH j i t) t) ∧
      (∀ j, ‖chartVector up axis P j‖ ≤ N) ∧
      (∀ j i, ‖QG j i‖ ≤ N) ∧ (∀ j i t, ‖QH j i t‖ ≤ N) := by
  let G' (j i : Fin 3) : L2Scalar :=
    ((chartSign up j : ℂ)*(chartSign up i : ℂ)) •
      chartPull up axis (G (Equiv.swap axis 2 j) (Equiv.swap axis 2 i))
  let H' (j i t : Fin 3) : L2Scalar :=
    ((chartSign up j : ℂ)*(chartSign up i : ℂ)*(chartSign up t : ℂ)) •
      chartPull up axis (H (Equiv.swap axis 2 j) (Equiv.swap axis 2 i) (Equiv.swap axis 2 t))
  have hcompact : ∀ j, CompactRepresentative (chartVector up axis P j) :=
    (chart_vector_compact_h2 up axis P hPc (fun j => ⟨G j,H j,hG j,hH j⟩)).1
  refine ⟨G',H',hcompact,?_,?_,?_,?_,?_⟩
  · intro j i
    have hh := chart_weak_partial up axis i (P (Equiv.swap axis 2 j))
      (G (Equiv.swap axis 2 j) (Equiv.swap axis 2 i)) (hG _ _)
    simpa only [chartVector,G',smul_smul] using weak_partial_smul (chartSign up j : ℂ) _ _ i hh
  · intro j i t
    have hh := chart_weak_partial up axis t (G (Equiv.swap axis 2 j) (Equiv.swap axis 2 i))
      (H (Equiv.swap axis 2 j) (Equiv.swap axis 2 i) (Equiv.swap axis 2 t)) (hH _ _ _)
    simpa only [G',H',smul_smul] using weak_partial_smul
      ((chartSign up j : ℂ)*(chartSign up i : ℂ)) _ _ t hh
  · intro j
    simpa only [chartVector,norm_smul,chart_sign_norm,one_mul,chart_pull_norm] using hP (Equiv.swap axis 2 j)
  · intro j i
    simpa only [G',norm_smul,norm_mul,chart_sign_norm,one_mul,chart_pull_norm] using hGn (Equiv.swap axis 2 j) (Equiv.swap axis 2 i)
  · intro j i t
    simpa only [H',norm_smul,norm_mul,chart_sign_norm,one_mul,chart_pull_norm] using hHn (Equiv.swap axis 2 j) (Equiv.swap axis 2 i) (Equiv.swap axis 2 t)

end OQ14.Packet05ChartH2Uniform
#print axioms OQ14.Packet05ChartH2Uniform.chart_pull_norm
#print axioms OQ14.Packet05ChartH2Uniform.chart_sign_norm
#print axioms OQ14.Packet05ChartH2Uniform.chart_vector_h2_uniform
