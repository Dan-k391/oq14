import SourcePairedCore

/-! Inverse stability for the converging actual paired-core material operators. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourcePairedInverse
open Filter Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Operator := VectorL2 →L[ℂ] VectorL2

theorem eventually_isUnit (A L : Operator) (T : ℕ → Operator) (hT : Tendsto T atTop (𝓝 L))
    (hL : IsUnit (A-L)) : ∀ᶠ r : ℕ in atTop,IsUnit (A-T r) :=
  (tendsto_const_nhds.sub hT).eventually (Units.isOpen.mem_nhds hL)

theorem inverse_tendsto (A L : Operator) (T : ℕ → Operator) (hT : Tendsto T atTop (𝓝 L))
    (hL : IsUnit (A-L)) :
    Tendsto (fun r : ℕ => Ring.inverse (A-T r)) atTop (𝓝 (Ring.inverse (A-L))) := by
  have hc := NormedRing.inverse_continuousAt hL.unit
  rw [hL.unit_spec] at hc
  exact hc.tendsto.comp (tendsto_const_nhds.sub hT)

theorem eventually_inverse_norm_le (A L : Operator) (T : ℕ → Operator) (hT : Tendsto T atTop (𝓝 L))
    (hL : IsUnit (A-L)) :
    ∀ᶠ r : ℕ in atTop,‖Ring.inverse (A-T r)‖ ≤ ‖Ring.inverse (A-L)‖+1 := by
  have h := (inverse_tendsto A L T hT hL).norm
  filter_upwards [h.eventually (eventually_le_nhds (lt_add_one _))] with r hr
  exact hr

theorem solution_tendsto (A L : Operator) (T : ℕ → Operator) (hT : Tendsto T atTop (𝓝 L))
    (hL : IsUnit (A-L)) (f : ℕ → VectorL2) (g : VectorL2) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun r : ℕ => Ring.inverse (A-T r) (f r)) atTop (𝓝 (Ring.inverse (A-L) g)) :=
  (isBoundedBilinearMap_apply.continuous.tendsto (Ring.inverse (A-L),g)).comp
    ((inverse_tendsto A L T hT hL).prodMk_nhds hf)

theorem eventually_solution_equation (A L : Operator) (T : ℕ → Operator) (hT : Tendsto T atTop (𝓝 L))
    (hL : IsUnit (A-L)) (f : ℕ → VectorL2) :
    ∀ᶠ r : ℕ in atTop,(A-T r) (Ring.inverse (A-T r) (f r))=f r := by
  filter_upwards [eventually_isUnit A L T hT hL] with r hr
  exact congrArg (fun S : Operator => S (f r)) (Ring.mul_inverse_cancel (A-T r) hr)

section Core
variable (c : StaticCoefficient.Coefficient) (d : BoundedMaterialKernel.SupportData c)
  (q : ℝ) (hq : 1≤q) (n : ℕ) (b : ℝ) (hb : 0<b) (A : Operator)

theorem core_eventually_isUnit (hL : IsUnit (A-SourcePairedCore.limitingOperator c d q hq n b hb)) :
    ∀ᶠ r : ℕ in atTop,IsUnit (A-SourcePairedCore.operator c d q hq n b hb r) :=
  eventually_isUnit A _ _ (SourcePairedCore.operator_limit c d q hq n b hb) hL

theorem core_inverse_tendsto (hL : IsUnit (A-SourcePairedCore.limitingOperator c d q hq n b hb)) :
    Tendsto (fun r : ℕ => Ring.inverse (A-SourcePairedCore.operator c d q hq n b hb r)) atTop
      (𝓝 (Ring.inverse (A-SourcePairedCore.limitingOperator c d q hq n b hb))) :=
  inverse_tendsto A _ _ (SourcePairedCore.operator_limit c d q hq n b hb) hL

theorem core_solution_tendsto (hL : IsUnit (A-SourcePairedCore.limitingOperator c d q hq n b hb))
    (f : ℕ → VectorL2) (g : VectorL2) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun r : ℕ => Ring.inverse (A-SourcePairedCore.operator c d q hq n b hb r) (f r)) atTop
      (𝓝 (Ring.inverse (A-SourcePairedCore.limitingOperator c d q hq n b hb) g)) :=
  solution_tendsto A _ _ (SourcePairedCore.operator_limit c d q hq n b hb) hL f g hf

end Core
end OQ14.SourcePairedInverse
#print axioms OQ14.SourcePairedInverse.eventually_isUnit
#print axioms OQ14.SourcePairedInverse.inverse_tendsto
#print axioms OQ14.SourcePairedInverse.eventually_inverse_norm_le
#print axioms OQ14.SourcePairedInverse.solution_tendsto
#print axioms OQ14.SourcePairedInverse.eventually_solution_equation
#print axioms OQ14.SourcePairedInverse.core_eventually_isUnit
#print axioms OQ14.SourcePairedInverse.core_inverse_tendsto
#print axioms OQ14.SourcePairedInverse.core_solution_tendsto
