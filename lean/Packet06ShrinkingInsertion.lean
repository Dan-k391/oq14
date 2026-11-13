import Packet06MaterialInsertion
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ShrinkingInsertion
open Filter MeasureTheory Set Metric OQ14.StaticCoefficient Packet06MaterialInsertion
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem shrinking_support_eventually_zero (d : ℕ → Coefficient) (center : ι → Space) (radius : ℕ → ℝ)
    (hr : Tendsto radius atTop (𝓝 0))
    (hsupport : ∀ n x, (∀ i, radius n < dist x (center i)) → (d n).value (VectorFourier.coordinateMap x) = 0) :
    ∀ᵐ ξ : StaticCoefficient.Space, ∀ᶠ n in atTop, (d n).value ξ = 0 := by
  have hne : ∀ᵐ x : Space, ∀ i, x ≠ center i := by
    apply ae_all_iff.mpr
    intro i
    apply ae_iff.mpr
    simp
  have hphys : ∀ᵐ x : Space, ∀ᶠ n in atTop, (d n).value (VectorFourier.coordinateMap x) = 0 := by
    filter_upwards [hne] with x hx
    have he : ∀ i, ∀ᶠ n in atTop, radius n < dist x (center i) := by
      intro i
      exact hr.eventually (Iio_mem_nhds (dist_pos.mpr (hx i)))
    have hall : ∀ᶠ n in atTop, ∀ i, radius n < dist x (center i) :=
      (eventually_all).mpr he
    filter_upwards [hall] with n hn
    exact hsupport n x hn
  have h := (MeasurePreserving.symm VectorFourier.coordinateMap VectorFourier.coordinateMap_preserving).quasiMeasurePreserving.ae hphys
  simpa only [MeasurableEquiv.apply_symm_apply] using h

theorem union_eventually_eq (c : Coefficient) (d : ℕ → Coefficient) (center : ι → Space)
    (radius : ℕ → ℝ) (hr : Tendsto radius atTop (𝓝 0))
    (hsupport : ∀ n x, (∀ i, radius n < dist x (center i)) → (d n).value (VectorFourier.coordinateMap x) = 0) :
    ∀ᵐ ξ : StaticCoefficient.Space, ∀ᶠ n in atTop,
      (unionCoefficient c (d n)).value ξ = c.value ξ := by
  filter_upwards [shrinking_support_eventually_zero d center radius hr hsupport] with ξ hξ
  filter_upwards [hξ] with n hn
  simp [unionCoefficient,hn,(c.nonnegative ξ)]
#print axioms OQ14.Packet06ShrinkingInsertion.shrinking_support_eventually_zero
#print axioms OQ14.Packet06ShrinkingInsertion.union_eventually_eq
end OQ14.Packet06ShrinkingInsertion
