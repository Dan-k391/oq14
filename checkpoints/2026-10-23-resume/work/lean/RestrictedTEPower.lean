import RestrictedTEAmplitude

/-! Genuine physical incoming power is faithful to the actual restricted TE fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEPower
open Complex MeasureTheory Maxwell HarmonicPolynomial DebyeRadialTrace
open RestrictedTEIncoming RestrictedTEAmplitude SymmetricHarmonicJets
abbrev Space := FourierL2.Space
abbrev Sphere := SphereReactionKernel.Sphere

theorem energy_continuous (A : Index →₀ ℂ) : Continuous (fun n : Sphere => energy (amplitude A n)) := by
  have hc (j : Fin 3) := (continuous_apply j).comp (amplitude_continuous A)
  unfold energy
  exact (((continuous_normSq.comp (hc 0)).add (continuous_normSq.comp (hc 1))).add
    (continuous_normSq.comp (hc 2)))

theorem power_zero_iff (A : Index →₀ ℂ) : physicalPower A=0 ↔ ∀ n : Sphere, amplitude A n=0 := by
  constructor
  · intro h
    have hi := FiniteTEIncomingPower.amplitude_energy_integrable A.support (fun q => q.val.1) polynomial (coefficient A)
    have he : (∫ n : Sphere, energy (amplitude A n) ∂SphereReactionKernel.surface)=0 := by
      change (∫ n : Sphere, energy (amplitude A n) ∂SphereReactionKernel.surface)/2=0 at h
      linarith
    have hz := SphereMeasure.continuous_zero_of_integral_zero _ (energy_continuous A) hi
      (fun n => FarFieldPower.energy_nonnegative _) he
    intro n
    exact (FarFieldPower.energy_zero_iff (amplitude A n)).mp (congrFun hz n)
  · intro h
    change (∫ n : Sphere, energy (amplitude A n) ∂SphereReactionKernel.surface)/2=0
    simp [h,energy]

theorem fields_zero_of_power_zero (A : Index →₀ ℂ) (h : physicalPower A=0) :
    DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A)=0 ∧
      DebyeMaxwell.teMagnetic 1 (RestrictedTEFields.potential 1 A)=0 := by
  have ha := (power_zero_iff A).mp h
  have hc : (2*Real.pi*I : ℂ)≠0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hd (n : Sphere) : density A n=0 := by
    ext j
    have hh := congrFun ((amplitude_eq A n).symm.trans (ha n)) j
    change (2*Real.pi*I : ℂ)*density A n j=0 at hh
    exact (mul_eq_zero.mp hh).resolve_left hc
  have he : DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A)=0 := by
    funext x j
    rw [electric_herglotz]
    simp [hd]
  refine ⟨he,?_⟩
  funext x j
  change (-I/1)*curl (DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A)) x j=0
  rw [he]
  fin_cases j <;> simp [curl,pd,dcoord]

theorem physical_power_pos (A : Index →₀ ℂ)
    (h : ∃ x : Space, ∃ j : Fin 3,
      DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A) x j≠0 ∨
      DebyeMaxwell.teMagnetic 1 (RestrictedTEFields.potential 1 A) x j≠0) :
    0<physicalPower A := by
  have hn := physical_power_nonnegative A
  have hne : physicalPower A≠0 := by
    intro hz
    obtain ⟨he,hh⟩ := fields_zero_of_power_zero A hz
    obtain ⟨x,j,hj⟩ := h
    simp only [he,hh,Pi.zero_apply,ne_eq,not_true_eq_false,or_self] at hj
  exact lt_of_le_of_ne hn (Ne.symm hne)

end OQ14.RestrictedTEPower
#print axioms OQ14.RestrictedTEPower.energy_continuous
#print axioms OQ14.RestrictedTEPower.power_zero_iff
#print axioms OQ14.RestrictedTEPower.fields_zero_of_power_zero
#print axioms OQ14.RestrictedTEPower.physical_power_pos
