import Packet05ChartH2

/-! Constitutive scalar-flux relations remain valid under the actual signed
Cartesian chart, with permuted and reflected vector components. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ChartConstitutive
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05ChartBasis OQ14.Packet05ChartLinearEquiv OQ14.Packet05ChartWeakGradient
  OQ14.Packet05ChartWeakDivergence

theorem chartVector_ae (up : Bool) (i j : Fin 3) (P : L2Vector) :
    (fun x => chartVector up i P j x) =ᵐ[volume] fun x =>
      (chartSign up j : ℂ) * P (Equiv.swap i 2 j) (inverseOriented up i x) := by
  filter_upwards [Lp.coeFn_smul (chartSign up j : ℂ) (chartPull up i (P (Equiv.swap i 2 j))),
    chartPull_ae up i (P (Equiv.swap i 2 j))] with x hs hp
  change ((chartSign up j : ℂ) • chartPull up i (P (Equiv.swap i 2 j))) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hp]

theorem chart_constitutive (up : Bool) (i : Fin 3) (P G Q : L2Vector) (ε : Space → ℂ)
    (hP : ∀ j, (fun x => P j x) =ᵐ[volume] fun x => ε x*(G j x+Q j x)) (j : Fin 3) :
    (fun x => chartVector up i P j x) =ᵐ[volume] fun x =>
      ε (inverseOriented up i x)*(chartVector up i G j x+chartVector up i Q j x) := by
  have hp := (oriented_inverse_measure_preserving up i).quasiMeasurePreserving.ae (hP (Equiv.swap i 2 j))
  filter_upwards [chartVector_ae up i j P,chartVector_ae up i j G,chartVector_ae up i j Q,hp] with x hp' hg hq hp
  rw [hp',hg,hq,hp]
  ring

end OQ14.Packet05ChartConstitutive
#print axioms OQ14.Packet05ChartConstitutive.chartVector_ae
#print axioms OQ14.Packet05ChartConstitutive.chart_constitutive
