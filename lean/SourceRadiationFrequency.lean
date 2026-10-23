import SourceTERadiation
import PuncturedMaxwellScaling

/-! The actual spatial outgoing source fields at arbitrary positive frequency. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.SourceRadiationFrequency
open Complex Filter MeasureTheory Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.SourceRadialSystem OQ14.PuncturedMaxwellScaling
open scoped Topology

def defect (k : ℝ) (E H : Field) (x : Space) : Vector :=
  (Complex.exp (-I*(k : ℂ)*(‖x‖ : ℂ))*(‖x‖ : ℂ)) •
    (H x-((‖x‖ : ℂ)⁻¹) • ModalInterface.tangent x (E x))

theorem defect_at_frequency (k : ℝ) (hk : 0<k) (E H : Field) (x : Space) :
    defect k (fieldAtFrequency k E) (fieldAtFrequency k H) x=
      (k : ℂ)⁻¹ • defect 1 E H (k • x) := by
  have hk0 : (k : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have ht : ((‖k • x‖ : ℂ)⁻¹) • ModalInterface.tangent (k • x) (E (k • x))=
      ((‖x‖ : ℂ)⁻¹) • ModalInterface.tangent x (E (k • x)) := by
    simpa only [inv_inv] using
      ModalScaling.normalized_tangent_dilate k⁻¹ (inv_pos.mpr hk) x (E (k • x))
  have hn : (‖k • x‖ : ℂ)=(k : ℂ)*(‖x‖ : ℂ) := by
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hk,Complex.ofReal_mul]
  unfold defect fieldAtFrequency
  rw [ht,smul_smul,hn]
  congr 1
  simp only [Complex.ofReal_one,mul_one]
  have he : -I*((k : ℂ)*(‖x‖ : ℂ))= -I*(k : ℂ)*(‖x‖ : ℂ) := by ring
  rw [he]
  field_simp
  ring

theorem defect_limit_at_frequency (k : ℝ) (hk : 0<k) (E H : Field)
    (hout : ∀ (γ : ℝ → Space), Tendsto (fun t => ‖γ t‖) atTop atTop →
      Tendsto (fun t => defect 1 E H (γ t)) atTop (𝓝 0))
    (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => defect k (fieldAtFrequency k E) (fieldAtFrequency k H) (γ t))
      atTop (𝓝 0) := by
  have hr : Tendsto (fun t => ‖k • γ t‖) atTop atTop := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hk] using hγ.const_mul_atTop hk
  have ht := (tendsto_const_nhds (x := (k : ℂ)⁻¹)).smul
    (hout (fun t => k • γ t) hr)
  simpa only [smul_zero,← defect_at_frequency k hk] using ht

theorem tm_radiation (d : Data) (p : Poly) (hp : p.IsHomogeneous d.l)
    (k : ℝ) (hk : 0<k) (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => defect k
      (fieldAtFrequency k (SourceUnclippedMaxwell.electric d p))
      (fieldAtFrequency k (SourceUnclippedMaxwell.magnetic d p)) (γ t)) atTop (𝓝 0) := by
  apply defect_limit_at_frequency k hk _ _ _ γ hγ
  intro η hη
  simpa only [defect,Complex.ofReal_one,mul_one,SourceRadiation.radiationDefect] using
    SourceRadiation.radiationDefect_limit d p hp η hη

theorem te_radiation (d : Data) (p : Poly) (hp : p.IsHomogeneous d.l)
    (k : ℝ) (hk : 0<k) (γ : ℝ → Space) (hγ : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    Tendsto (fun t => defect k
      (fieldAtFrequency k (SourceGeneralMaxwell.teElectric d p))
      (fieldAtFrequency k (SourceGeneralMaxwell.teMagnetic d p)) (γ t)) atTop (𝓝 0) := by
  apply defect_limit_at_frequency k hk _ _ _ γ hγ
  intro η hη
  simpa only [defect,Complex.ofReal_one,mul_one,SourceTERadiation.radiationDefect] using
    SourceTERadiation.radiationDefect_limit d p hp η hη

/-- Both actual equations on punctured space together with the outgoing spatial condition. -/
def OutgoingPuncturedMaxwell (k : ℝ) (ε : Space → ℂ) (E H : Field) : Prop :=
  (∀ (φ : Space → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ → 0∉tsupport φ →
    weakCurlPairing E φ=(fun j => ∫ x,(I*(k : ℂ)*H x j)*φ x) ∧
    weakCurlPairing H φ=(fun j => ∫ x,(-I*(k : ℂ)*ε x*E x j)*φ x)) ∧
  (∀ (γ : ℝ → Space), Tendsto (fun t => ‖γ t‖) atTop atTop →
    Tendsto (fun t => defect k E H (γ t)) atTop (𝓝 0))

theorem tm_outgoing_maxwell (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (p : Poly) (hp : p.IsHomogeneous d.l) (hh : formalLaplacian p=0) (k : ℝ) (hk : 0<k) :
    OutgoingPuncturedMaxwell k (coefficientAtFrequency k (sigma d))
      (fieldAtFrequency k (SourceUnclippedMaxwell.electric d p))
      (fieldAtFrequency k (SourceUnclippedMaxwell.magnetic d p)) :=
  ⟨tm_at_positive_frequency d hdisp p hp hh k hk,tm_radiation d p hp k hk⟩

theorem te_outgoing_maxwell (d : Data) (hσ : ∀ g∈d.gs,g.σ=1)
    (p : Poly) (hp : p.IsHomogeneous d.l) (hh : formalLaplacian p=0) (k : ℝ) (hk : 0<k) :
    OutgoingPuncturedMaxwell k (coefficientAtFrequency k (SourceGeneralMaxwell.mu d))
      (fieldAtFrequency k (SourceGeneralMaxwell.teElectric d p))
      (fieldAtFrequency k (SourceGeneralMaxwell.teMagnetic d p)) :=
  ⟨te_at_positive_frequency d hσ p hp hh k hk,te_radiation d p hp k hk⟩

end OQ14.SourceRadiationFrequency

#print axioms OQ14.SourceRadiationFrequency.defect_at_frequency
#print axioms OQ14.SourceRadiationFrequency.defect_limit_at_frequency
#print axioms OQ14.SourceRadiationFrequency.tm_radiation
#print axioms OQ14.SourceRadiationFrequency.te_radiation
#print axioms OQ14.SourceRadiationFrequency.tm_outgoing_maxwell
#print axioms OQ14.SourceRadiationFrequency.te_outgoing_maxwell
