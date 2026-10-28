import WeightedAnnulusDatum

/-! Zero extension of continuous fields on the compact physical unit ball to L². -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.CompactFieldDatum
open MeasureTheory Set Metric Filter OQ14.Maxwell
attribute [local instance] Classical.propDecidable
open scoped Topology

abbrev Core : Set Space := closedBall (0 : Space) 1

theorem core_compact : IsCompact Core := isCompact_closedBall 0 1
instance : CompactSpace Core := isCompact_iff_compactSpace.mp core_compact

def extension (f : C(Core, ℂ)) (x : Space) : ℂ :=
  if hx : x ∈ Core then f ⟨x, hx⟩ else 0

theorem extension_measurable (f : C(Core, ℂ)) : Measurable (extension f) :=
  f.continuous.measurable.dite measurable_const core_compact.measurableSet

theorem extension_bound (f : C(Core, ℂ)) (x : Space) : ‖extension f x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ Core
  · simpa [extension, hx] using f.norm_coe_le_norm ⟨x, hx⟩
  · simp [extension, hx]

theorem extension_memLp (f : C(Core, ℂ)) : MemLp (extension f) 2 volume := by
  have hs : HasCompactSupport (extension f) := by
    apply HasCompactSupport.intro' core_compact core_compact.isClosed
    intro x hx
    simp [extension, hx]
  exact hs.memLp_of_bound (extension_measurable f).aestronglyMeasurable _
    (Eventually.of_forall (extension_bound f))

def scalar (f : C(Core, ℂ)) : FourierL2.ScalarL2 :=
  (extension_memLp f).toLp (extension f)

theorem scalar_ae (f : C(Core, ℂ)) : (scalar f : Space → ℂ) =ᵐ[volume] extension f :=
  (extension_memLp f).coeFn_toLp

def reference : FourierL2.ScalarL2 :=
  indicatorConstLp 2 core_compact.measurableSet core_compact.measure_lt_top.ne (1 : ℂ)

theorem scalar_norm (f : C(Core, ℂ)) : ‖scalar f‖ ≤ ‖reference‖ * ‖f‖ := by
  have h : ‖scalar f‖ ≤ ‖f‖ * ‖reference‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [scalar_ae f,
      (indicatorConstLp_coeFn (p := 2) (hs := core_compact.measurableSet)
        (hμs := core_compact.measure_lt_top.ne) (c := (1 : ℂ)))] with x hx href
    change reference x = Core.indicator (fun _ => (1 : ℂ)) x at href
    rw [hx, href]
    by_cases ha : x ∈ Core
    · simpa [ha] using extension_bound f x
    · simp [ha, extension]
  simpa [mul_comm] using h

def scalarLinear : C(Core, ℂ) →ₗ[ℂ] FourierL2.ScalarL2 where
  toFun := scalar
  map_add' f g := by
    apply Lp.ext
    filter_upwards [scalar_ae (f + g), scalar_ae f, scalar_ae g,
      Lp.coeFn_add (scalar f) (scalar g)] with x hfg hf hg ha
    rw [hfg, ha]
    simp only [Pi.add_apply]
    rw [hf, hg]
    dsimp [extension]
    split_ifs <;> simp
  map_smul' z f := by
    apply Lp.ext
    filter_upwards [scalar_ae (z • f), scalar_ae f,
      Lp.coeFn_smul z (scalar f)] with x hzf hf hz
    change scalar (z • f) x = (z • scalar f) x
    rw [hzf, hz]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hf]
    dsimp [extension]
    split_ifs <;> simp

def scalarMap : C(Core, ℂ) →L[ℂ] FourierL2.ScalarL2 :=
  scalarLinear.mkContinuous ‖reference‖ scalar_norm

theorem scalarMap_ae (f : C(Core, ℂ)) :
    (scalarMap f : Space → ℂ) =ᵐ[volume] extension f := scalar_ae f

theorem extension_on (f : C(Core, ℂ)) (x : Space) (hx : x ∈ Core) :
    extension f x = f ⟨x, hx⟩ := by simp [extension, hx]

theorem extension_off (f : C(Core, ℂ)) (x : Space) (hx : x ∉ Core) :
    extension f x = 0 := by simp [extension, hx]

end OQ14.CompactFieldDatum

#print axioms OQ14.CompactFieldDatum.core_compact
#print axioms OQ14.CompactFieldDatum.extension_measurable
#print axioms OQ14.CompactFieldDatum.extension_bound
#print axioms OQ14.CompactFieldDatum.extension_memLp
#print axioms OQ14.CompactFieldDatum.scalar_ae
#print axioms OQ14.CompactFieldDatum.scalar_norm
#print axioms OQ14.CompactFieldDatum.scalarMap_ae
#print axioms OQ14.CompactFieldDatum.extension_on
#print axioms OQ14.CompactFieldDatum.extension_off
