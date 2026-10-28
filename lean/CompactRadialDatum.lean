import RegularizedOutgoing
import RadialFiniteSpan

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.CompactRadialDatum
open MeasureTheory Set Metric Filter OQ14.PolarMomentOperator
attribute [local instance] Classical.propDecidable
open scoped Topology

abbrev Core (a b : ℝ) := Icc a b
instance (a b : ℝ) : CompactSpace (Core a b) := isCompact_iff_compactSpace.mp isCompact_Icc

def extension (a b : ℝ) (f : C(Core a b, ℂ)) (x : ℝ) : ℂ :=
  if hx : x ∈ Core a b then f ⟨x, hx⟩ else 0

theorem extension_measurable (a b : ℝ) (f : C(Core a b, ℂ)) : Measurable (extension a b f) :=
  f.continuous.measurable.dite measurable_const measurableSet_Icc

theorem extension_bound (a b : ℝ) (f : C(Core a b, ℂ)) (x : ℝ) : ‖extension a b f x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ Core a b
  · simpa [extension, hx] using f.norm_coe_le_norm ⟨x, hx⟩
  · simp [extension, hx]

theorem extension_memLp (a b : ℝ) (f : C(Core a b, ℂ)) :
    MemLp (extension a b f) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hs : HasCompactSupport (extension a b f) := by
    apply HasCompactSupport.intro' (isCompact_Icc : IsCompact (Core a b)) isClosed_Icc
    intro x hx
    simp [extension, hx]
  exact hs.memLp_of_bound (extension_measurable a b f).aestronglyMeasurable _
    (Eventually.of_forall (extension_bound a b f))

def scalar (a b : ℝ) (f : C(Core a b, ℂ)) : RadialL2 :=
  (extension_memLp a b f).toLp (extension a b f)

theorem scalar_ae (a b : ℝ) (f : C(Core a b, ℂ)) :
    (scalar a b f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] extension a b f :=
  (extension_memLp a b f).coeFn_toLp

def reference (a b : ℝ) : RadialL2 := indicatorConstLp 2 (s := Icc a b) measurableSet_Icc
  ((isCompact_Icc : IsCompact (Icc a b)).measure_lt_top (μ := volume.restrict (Ioi (0 : ℝ)))).ne (1 : ℂ)



theorem scalar_norm (a b : ℝ) (f : C(Core a b, ℂ)) : ‖scalar a b f‖ ≤ ‖reference a b‖ * ‖f‖ := by
  have h : ‖scalar a b f‖ ≤ ‖f‖ * ‖reference a b‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [scalar_ae a b f,
      (indicatorConstLp_coeFn (p := 2) (s := Icc a b) (hs := measurableSet_Icc)
        (hμs := ((isCompact_Icc : IsCompact (Icc a b)).measure_lt_top
          (μ := volume.restrict (Ioi (0 : ℝ)))).ne) (c := (1 : ℂ)))] with x hx href
    change reference a b x = (Icc a b).indicator (fun _ => (1 : ℂ)) x at href
    rw [hx, href]
    by_cases ha : x ∈ Core a b
    · simpa [ha] using extension_bound a b f x
    · simp [ha, extension]
  simpa [mul_comm] using h

def scalarLinear (a b : ℝ) : C(Core a b, ℂ) →ₗ[ℂ] RadialL2 where
  toFun := scalar a b
  map_add' f g := by
    apply Lp.ext
    filter_upwards [scalar_ae a b (f + g), scalar_ae a b f, scalar_ae a b g,
      Lp.coeFn_add (scalar a b f) (scalar a b g)] with x hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply]
    rw [hf, hg]
    dsimp [extension]
    split_ifs <;> simp
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [scalar_ae a b (z • f), scalar_ae a b f,
      Lp.coeFn_smul z (scalar a b f)] with x hzf hf hz
    change scalar a b (z • f) x = (z • scalar a b f) x
    rw [hzf, hz]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    dsimp [extension]
    split_ifs <;> simp

def scalarMap (a b : ℝ) : C(Core a b, ℂ) →L[ℂ] RadialL2 :=
  (scalarLinear a b).mkContinuous ‖reference a b‖ (scalar_norm a b)

theorem scalarMap_ae (a b : ℝ) (f : C(Core a b, ℂ)) :
    (scalarMap a b f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] extension a b f := scalar_ae a b f

#print axioms OQ14.CompactRadialDatum.scalarMap_ae
#print axioms OQ14.CompactRadialDatum.scalar_norm
end OQ14.CompactRadialDatum
