import ModalShell

/-! # Actual shell-field residue of the spherical matching response

The output is a genuine L2 electric/magnetic field on a bounded shell.
The residue asymptotic is in the operator norm for the two matching data.
This radial response is not identified here with the full Maxwell resolvent.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.ModalFieldResidue

open Complex Filter OQ14.ModalAlgebra OQ14.ModalMatching OQ14.ModalInterface OQ14.ModalShell
open scoped Topology

def outgoingCoefficient (n : ℂ) (k : Frequency) : Amplitudes →L[ℂ] ℂ :=
  (solve 1 n k.1 (1,0)).2 • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (solve 1 n k.1 (0,1)).2 • ContinuousLinearMap.snd ℂ ℂ ℂ

def residueCoefficient (n : ℂ) (k : Frequency) : Amplitudes →L[ℂ] ℂ :=
  (residue 1 n k.1 (1,0)).2 • ContinuousLinearMap.fst ℂ ℂ ℂ +
    (residue 1 n k.1 (0,1)).2 • ContinuousLinearMap.snd ℂ ℂ ℂ

theorem outgoingCoefficient_apply (n : ℂ) (k : Frequency) (f : Amplitudes) :
    outgoingCoefficient n k f = (solve 1 n k.1 f).2 := by
  simp only [outgoingCoefficient, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, solve, adjugate]
  ring

theorem residueCoefficient_apply (n : ℂ) (k : Frequency) (f : Amplitudes) :
    residueCoefficient n k f = (residue 1 n k.1 f).2 := by
  simp only [residueCoefficient, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, residue, adjugate]
  ring

def responseOperator (n : ℂ) (k : Frequency) : Amplitudes →L[ℂ] ShellL2 :=
  (outgoingCoefficient n k).smulRight (unitL2 k)

def residueOperator (n : ℂ) (k : Frequency) : Amplitudes →L[ℂ] ShellL2 :=
  (residueCoefficient n k).smulRight (unitL2 k)

theorem responseOperator_apply (n : ℂ) (k : Frequency) (f : Amplitudes) :
    responseOperator n k f = (solve 1 n k.1 f).2 • unitL2 k := by
  simp only [responseOperator, ContinuousLinearMap.smulRight_apply, outgoingCoefficient_apply]

theorem residueOperator_apply (n : ℂ) (k : Frequency) (f : Amplitudes) :
    residueOperator n k f = (residue 1 n k.1 f).2 • unitL2 k := by
  simp only [residueOperator, ContinuousLinearMap.smulRight_apply, residueCoefficient_apply]

theorem responseOperator_actual (n : ℂ) (k : Frequency) (f : Amplitudes) :
    (responseOperator n k f : Shell → PairVector) =ᵐ[shellMeasure] fun x =>
      (outerE k.1 (solve 1 n k.1 f).2 x.1, outerH k.1 (solve 1 n k.1 f).2 x.1) := by
  rw [responseOperator_apply]
  exact scaled_unitL2_ae k _

theorem residueOperator_actual (n : ℂ) (k : Frequency) (f : Amplitudes) :
    (residueOperator n k f : Shell → PairVector) =ᵐ[shellMeasure] fun x =>
      (outerE k.1 (residue 1 n k.1 f).2 x.1, outerH k.1 (residue 1 n k.1 f).2 x.1) := by
  rw [residueOperator_apply]
  exact scaled_unitL2_ae k _

theorem frequency_punctured_tendsto (k₀ : Frequency) :
    Tendsto (fun k : Frequency => k.1) (𝓝[≠] k₀) (𝓝[≠] k₀.1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact continuous_subtype_val.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with k hk
    change k.1 ≠ k₀.1
    intro h
    exact hk (Subtype.ext h)

theorem outgoingCoefficient_residue_limit (n : ℂ) (k₀ : Frequency) (hn : n ≠ 0)
    (hd : tmDet 1 n k₀.1 = 0) (hs : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    Tendsto (fun k : Frequency => (k.1-k₀.1) • outgoingCoefficient n k) (𝓝[≠] k₀)
      (𝓝 (residueCoefficient n k₀)) := by
  have hl (f : Amplitudes) :
      Tendsto (fun k : Frequency => (k.1-k₀.1) * (solve 1 n k.1 f).2) (𝓝[≠] k₀)
        (𝓝 (residue 1 n k₀.1 f).2) := by
    have ht := (continuous_snd.tendsto _).comp
      ((solve_residue_limit 1 n k₀.1 hn k₀.property hd hs f).comp
        (frequency_punctured_tendsto k₀))
    simpa only [Prod.smul_snd, smul_eq_mul] using ht
  have h0 := (hl (1,0)).smul
    (tendsto_const_nhds (x := ContinuousLinearMap.fst ℂ ℂ ℂ))
  have h1 := (hl (0,1)).smul
    (tendsto_const_nhds (x := ContinuousLinearMap.snd ℂ ℂ ℂ))
  simpa only [outgoingCoefficient, residueCoefficient, smul_add, smul_smul] using h0.add h1

/-- A genuine operator-norm residue limit for the actual bounded-shell
electric/magnetic response. This limit does not by itself assert
Banach-valued holomorphy of the unscaled family. -/
theorem responseOperator_residue_limit (n : ℂ) (k₀ : Frequency) (hn : n ≠ 0)
    (hd : tmDet 1 n k₀.1 = 0) (hs : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    Tendsto (fun k : Frequency => (k.1-k₀.1) • responseOperator n k) (𝓝[≠] k₀)
      (𝓝 (residueOperator n k₀)) := by
  have hc := outgoingCoefficient_residue_limit n k₀ hn hd hs
  have hu := unitL2_continuous.continuousAt.tendsto.mono_left
    (show 𝓝[≠] k₀ ≤ 𝓝 k₀ from nhdsWithin_le_nhds)
  have hb : Continuous (fun p : (Amplitudes →L[ℂ] ℂ) × ShellL2 => p.1.smulRight p.2) :=
    (ContinuousLinearMap.smulRightL ℂ Amplitudes ShellL2).continuous₂
  have ht := hb.continuousAt.tendsto.comp (hc.prodMk_nhds hu)
  convert ht using 1
  funext k
  apply ContinuousLinearMap.ext
  intro f
  simp only [Function.comp_def, responseOperator, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, smul_smul]

theorem response_determinant_eventually_nonzero (n : ℂ) (k₀ : Frequency) (hn : n ≠ 0)
    (hd : tmDet 1 n k₀.1 = 0) (hs : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    ∀ᶠ k : Frequency in 𝓝[≠] k₀, tmDet 1 n k.1 ≠ 0 :=
  (frequency_punctured_tendsto k₀).eventually
    (determinant_eventually_nonzero 1 n k₀.1 hn k₀.property hd hs)

theorem residueOperator_nonzero (n : ℂ) (k₀ : Frequency) (hn : n ≠ 0)
    (hd : tmDet 1 n k₀.1 = 0) (hs : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    residueOperator n k₀ ≠ 0 := by
  obtain ⟨f, hf⟩ := residue_nonzero 1 n k₀.1 k₀.property hs
  have hb := (matching_nonzero_amplitudes 1 n k₀.1 hn k₀.property
    (residue 1 n k₀.1 f) hf (residue_in_matching_kernel 1 n k₀.1 hd f)).2
  intro hz
  have he := congrArg (fun T : Amplitudes →L[ℂ] ShellL2 => T f) hz
  change residueOperator n k₀ f = 0 at he
  rw [residueOperator_apply] at he
  exact (smul_ne_zero hb (unitL2_ne_zero k₀)) he

theorem residueOperator_range_line (n : ℂ) (k₀ : Frequency) :
    ∀ f : Amplitudes, ∃ c : ℂ, residueOperator n k₀ f = c • unitL2 k₀ := by
  intro f
  exact ⟨(residue 1 n k₀.1 f).2, residueOperator_apply n k₀ f⟩

theorem exists_high_quality_field_residue (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k₀ : Frequency, L < k₀.1.re ∧ k₀.1.im < 0 ∧
      Q < k₀.1.re / (-2*k₀.1.im) ∧
      residueOperator (n : ℂ) k₀ ≠ 0 ∧
      (∀ᶠ k : Frequency in 𝓝[≠] k₀, tmDet 1 (n : ℂ) k.1 ≠ 0) ∧
      Tendsto (fun k : Frequency => (k.1-k₀.1) • responseOperator (n : ℂ) k)
        (𝓝[≠] k₀) (𝓝 (residueOperator (n : ℂ) k₀)) := by
  obtain ⟨k, hk, hd, hs, hL, hi, hratio⟩ :=
    OQ14.ModalAsymptotics.tm_high_quality_zeros 1 n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  exact ⟨⟨k,hk⟩, hL, hi, hratio,
    residueOperator_nonzero (n : ℂ) ⟨k,hk⟩ hn0 hd hs,
    response_determinant_eventually_nonzero (n : ℂ) ⟨k,hk⟩ hn0 hd hs,
    responseOperator_residue_limit (n : ℂ) ⟨k,hk⟩ hn0 hd hs⟩

end OQ14.ModalFieldResidue


#print axioms OQ14.ModalFieldResidue.outgoingCoefficient_apply
#print axioms OQ14.ModalFieldResidue.residueCoefficient_apply
#print axioms OQ14.ModalFieldResidue.responseOperator_apply
#print axioms OQ14.ModalFieldResidue.residueOperator_apply
#print axioms OQ14.ModalFieldResidue.responseOperator_actual
#print axioms OQ14.ModalFieldResidue.residueOperator_actual
#print axioms OQ14.ModalFieldResidue.frequency_punctured_tendsto
#print axioms OQ14.ModalFieldResidue.outgoingCoefficient_residue_limit
#print axioms OQ14.ModalFieldResidue.responseOperator_residue_limit
#print axioms OQ14.ModalFieldResidue.response_determinant_eventually_nonzero
#print axioms OQ14.ModalFieldResidue.residueOperator_nonzero
#print axioms OQ14.ModalFieldResidue.residueOperator_range_line
#print axioms OQ14.ModalFieldResidue.exists_high_quality_field_residue
