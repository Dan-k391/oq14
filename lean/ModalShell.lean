import ModalLocal
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Actual outgoing spherical fields as a continuous shell-L2 family

The shell measure is the pullback of ordinary three-dimensional volume.
Both electric and magnetic fields are retained. Their L2 realization is
continuous in every nonzero complex frequency and is genuinely nonzero.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.ModalShell

open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalAlgebra
  OQ14.ModalWronskian OQ14.ModalDipole OQ14.ModalInterface
open scoped Topology

def shell : Set Space := {x | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}

theorem shell_compact : IsCompact shell := by
  apply (isCompact_closedBall (0 : Space) 2).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    exact mem_closedBall_zero_iff.mpr hx.2

abbrev Shell := shell
abbrev Frequency := {k : ℂ // k ≠ 0}
abbrev PairVector := Vector × Vector

instance : CompactSpace Shell := isCompact_iff_compactSpace.mp shell_compact

def shellMeasure : Measure Shell := volume.comap ((↑) : Shell → Space)

theorem shellMeasure_map :
    shellMeasure.map ((↑) : Shell → Space) = volume.restrict shell :=
  map_comap_subtype_coe shell_compact.measurableSet volume

instance : IsFiniteMeasure shellMeasure where
  measure_univ_lt_top := by
    rw [shellMeasure, comap_subtype_coe_apply shell_compact.measurableSet,
      Set.image_univ, Subtype.range_coe]
    exact shell_compact.measure_lt_top

abbrev ShellL2 := Lp PairVector 2 shellMeasure

theorem shell_radius_ne_zero (x : Shell) : (‖(x : Space)‖ : ℂ) ≠ 0 := by
  apply ofReal_ne_zero.mpr
  have h := x.property.1
  linarith

def unitPair (k : Frequency) (x : Shell) : PairVector :=
  (outerE k.1 1 x.1, outerH k.1 1 x.1)

theorem unitPair_joint_continuous :
    Continuous (fun p : Frequency × Shell => unitPair p.1 p.2) := by
  have hk : Continuous (fun p : Frequency × Shell => p.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hr : Continuous (fun p : Frequency × Shell => (‖(p.2 : Space)‖ : ℂ)) :=
    continuous_ofReal.comp ((continuous_subtype_val.comp continuous_snd).norm)
  have hr0 (p : Frequency × Shell) : (‖(p.2 : Space)‖ : ℂ) ≠ 0 := shell_radius_ne_zero p.2
  have hp := hk.mul hr
  have hu : Continuous (fun p : Frequency × Shell => xi 1 (p.1.1 * ‖(p.2 : Space)‖)) :=
    continuous_iff_continuousAt.mpr fun p =>
      ContinuousAt.comp (f := fun q : Frequency × Shell => q.1.1 * ‖(q.2 : Space)‖)
        (g := xi 1) (xi_hasDerivAt 1 _ (mul_ne_zero p.1.property (hr0 p))).continuousAt
        hp.continuousAt
  have hd : Continuous (fun p : Frequency × Shell => xiD 1 (p.1.1 * ‖(p.2 : Space)‖)) :=
    continuous_iff_continuousAt.mpr fun p =>
      ContinuousAt.comp (f := fun q : Frequency × Shell => q.1.1 * ‖(q.2 : Space)‖)
        (g := xiD 1) (xiD_hasDerivAt 1 _ (mul_ne_zero p.1.property (hr0 p))).continuousAt
        hp.continuousAt
  have hA := (hk.mul hd).div hr hr0
  have hB := (((continuous_const : Continuous (fun _ : Frequency × Shell => (2 : ℂ))).mul hu).div
    (hr.pow 4) (fun p => pow_ne_zero _ (hr0 p))).sub
    ((hk.mul hd).div (hr.pow 3) (fun p => pow_ne_zero _ (hr0 p)))
  have hC := (((continuous_const : Continuous (fun _ : Frequency × Shell => I)).mul
    (hk.pow 2)).div hk (fun p => p.1.property)).mul hu |>.div
    (hr.pow 2) (fun p => pow_ne_zero _ (hr0 p))
  have hx (j : Fin 3) : Continuous (fun p : Frequency × Shell => ((p.2 : Space) j : ℂ)) :=
    (coordinate j).continuous.comp (continuous_subtype_val.comp continuous_snd)
  apply Continuous.prodMk
  · apply continuous_pi
    intro j
    fin_cases j
    · simpa [unitPair, outerE, outgoingE, dipoleE, axisField, electricB, scaledRadial,
        scaledRadialD] using (hB.mul (hx 2)).mul (hx 0)
    · simpa [unitPair, outerE, outgoingE, dipoleE, axisField, electricB, scaledRadial,
        scaledRadialD] using (hB.mul (hx 2)).mul (hx 1)
    · simpa [unitPair, outerE, outgoingE, dipoleE, axisField, electricA, electricB,
        scaledRadial, scaledRadialD] using hA.add ((hB.mul (hx 2)).mul (hx 2))
  · apply continuous_pi
    intro j
    fin_cases j
    · simpa [unitPair, outerH, outgoingH, dipoleH, swirlField, magneticC, scaledRadial] using
        hC.mul (hx 1)
    · simpa [unitPair, outerH, outgoingH, dipoleH, swirlField, magneticC, scaledRadial] using
        hC.neg.mul (hx 0)
    · simpa [unitPair, outerH, outgoingH, dipoleH, swirlField] using
        (continuous_const : Continuous (fun _ : Frequency × Shell => (0 : ℂ)))

def unitContinuous (k : Frequency) : C(Shell, PairVector) :=
  ⟨unitPair k, Continuous.uncurry_left (f := unitPair) k unitPair_joint_continuous⟩

theorem unitContinuous_continuous : Continuous unitContinuous :=
  ContinuousMap.continuous_of_continuous_uncurry _ unitPair_joint_continuous

def unitL2 (k : Frequency) : ShellL2 :=
  ContinuousMap.toLp 2 shellMeasure ℂ (unitContinuous k)

theorem unitL2_ae (k : Frequency) : (unitL2 k : Shell → PairVector) =ᵐ[shellMeasure] unitPair k :=
  ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) shellMeasure (unitContinuous k)

theorem unitL2_continuous : Continuous unitL2 :=
  (ContinuousMap.toLp 2 shellMeasure ℂ).continuous.comp unitContinuous_continuous

theorem scaled_unitL2_ae (k : Frequency) (b : ℂ) :
    ((b • unitL2 k : ShellL2) : Shell → PairVector) =ᵐ[shellMeasure]
      fun x => (outerE k.1 b x.1, outerH k.1 b x.1) := by
  filter_upwards [Lp.coeFn_smul b (unitL2 k), unitL2_ae k] with x hx hu
  rw [hx]
  simp only [Pi.smul_apply, hu]
  simp [unitPair, outerE, outerH, Prod.smul_mk]

theorem unitL2_ne_zero (k : Frequency) : unitL2 k ≠ 0 := by
  intro hz
  have ha : unitPair k =ᵐ[shellMeasure] (fun _ => (0 : PairVector)) := by
    apply (unitL2_ae k).symm.trans
    rw [hz]
    exact Lp.coeFn_zero PairVector 2 shellMeasure
  have hb : (fun x : Space => (outerE k.1 1 x, outerH k.1 1 x))
      =ᵐ[volume.restrict shell] (fun _ => (0 : PairVector)) :=
    (ae_restrict_iff_subtype shell_compact.measurableSet).mpr ha
  have hc : ContinuousOn (fun x : Space => (outerE k.1 1 x, outerH k.1 1 x)) shell :=
    continuousOn_iff_continuous_restrict.mpr (unitContinuous k).continuous
  let V : Set Space := {x | 1 < ‖x‖ ∧ ‖x‖ < 2}
  have hV : IsOpen V :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hs : V ⊆ shell := fun _ hx => ⟨hx.1.le, hx.2.le⟩
  have he := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset hs hb)
    hV (hc.mono hs) continuousOn_const
  obtain ⟨x, hx, ht⟩ := outer_traces_not_both_zero k.1 1 k.property one_ne_zero (3/2) (by norm_num)
  have hxV : x ∈ V := by dsimp [V]; rw [hx]; constructor <;> norm_num
  have heq := he hxV
  have hE : outerE k.1 1 x = 0 := congrArg Prod.fst heq
  have hH : outerH k.1 1 x = 0 := congrArg Prod.snd heq
  rcases ht with ht | ht
  · exact ht (by simp [hE, tangent])
  · exact ht (by simp [hH, tangent])

end OQ14.ModalShell

#print axioms OQ14.ModalShell.shell_compact
#print axioms OQ14.ModalShell.shellMeasure_map
#print axioms OQ14.ModalShell.shell_radius_ne_zero
#print axioms OQ14.ModalShell.unitPair_joint_continuous
#print axioms OQ14.ModalShell.unitContinuous_continuous
#print axioms OQ14.ModalShell.unitL2_ae
#print axioms OQ14.ModalShell.unitL2_continuous
#print axioms OQ14.ModalShell.scaled_unitL2_ae
#print axioms OQ14.ModalShell.unitL2_ne_zero
