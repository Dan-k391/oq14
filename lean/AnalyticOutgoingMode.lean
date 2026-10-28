import CompactRadialDatum

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.AnalyticOutgoingMode
open Complex MeasureTheory Set Filter OQ14.CompactRadialDatum OQ14.RegularizedOutgoing
  OQ14.PolarMomentOperator
open scoped Topology

def radius (a b : ℝ) : C(Core a b, ℂ) :=
  ⟨fun r => ((r : ℝ) : ℂ), Complex.continuous_ofReal.comp continuous_subtype_val⟩

def inversePower (a b : ℝ) (ha : 0 < a) (l : ℕ) : C(Core a b, ℂ) :=
  ⟨fun r => (((r : ℝ) : ℂ)^l)⁻¹,
    ((radius a b).continuous.pow l).inv₀ (fun r => pow_ne_zero l
      (ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le ha r.property.1))))⟩

def modeCore (a b : ℝ) (ha : 0 < a) (l : ℕ) (z : ℂ) : C(Core a b, ℂ) :=
  CompactEntireLift.lift (radius a b) (profile l) (profile_differentiable l).continuous z * inversePower a b ha l

def mode (a b : ℝ) (ha : 0 < a) (l : ℕ) (z : ℂ) : RadialL2 :=
  scalarMap a b (modeCore a b ha l z)

theorem mode_analytic (a b : ℝ) (ha : 0 < a) (l : ℕ) (z : ℂ) :
    AnalyticAt ℂ (mode a b ha l) z := by
  exact ((scalarMap a b).analyticAt _).comp
    ((CompactEntireLift.analyticAt_lift (radius a b) (profile l) (profile_differentiable l) z).mul analyticAt_const)

theorem mode_actual (a b : ℝ) (ha : 0 < a) (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    (mode a b ha l z : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (Icc a b).indicator (fun r => z^l * RadialRellich.outgoing l z r) := by
  filter_upwards [scalarMap_ae a b (modeCore a b ha l z)] with r hr
  change (scalarMap a b (modeCore a b ha l z)) r = _
  rw [hr]
  by_cases h : r ∈ Icc a b
  · have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le ha h.1))
    simp only [extension, h, dif_pos, indicator_of_mem, modeCore, ContinuousMap.mul_apply,
      CompactEntireLift.lift, radius, inversePower, ContinuousMap.coe_mk, RadialRellich.outgoing]
    rw [profile_eq l (z*r) (mul_ne_zero hz hr0), mul_pow]
    field_simp
    ring
  · simp [extension, h]

#print axioms OQ14.AnalyticOutgoingMode.mode_analytic
#print axioms OQ14.AnalyticOutgoingMode.mode_actual
end OQ14.AnalyticOutgoingMode


