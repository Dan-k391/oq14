import SourceGeneralMaxwell

/-! Actual electric and magnetic polarizations in ordinary layered dielectrics. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.SourceDielectricMaxwell
open MeasureTheory Set OQ14.Maxwell OQ14.RadialStack OQ14.SourceRadialSystem

theorem sigma_one (d : Data) (hσ : ∀ g∈d.gs,g.σ=1) (r : ℝ) : sigma d r=1 := by
  have hsel {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
      (hh : ∀ g∈gs,g.σ=1) (hr : R<r) (hrX : r≤X) : RadialGluing.sigmaAt gs r=1 := by
    induction h with
    | nil R => exact (not_lt_of_ge hrX hr).elim
    | cons g gs R h ih =>
      by_cases hg : g.a<r
      · simp only [RadialGluing.sigmaAt,if_pos hg,hh g List.mem_cons_self]
      · simp only [RadialGluing.sigmaAt,if_neg hg]
        exact ih (fun g hg => hh g (List.mem_cons_of_mem _ hg)) hr (not_lt.mp hg)
  by_cases hR : r≤d.R
  · simp only [sigma,SourceRadialSystem.extend,if_pos hR]
  · by_cases hX : r≤d.X
    · simp only [sigma,SourceRadialSystem.extend,if_neg hR,if_pos hX,
        hsel d.chain hσ (not_le.mp hR) hX,Complex.ofReal_one]
    · simp only [sigma,SourceRadialSystem.extend,if_neg hR,if_neg hX]

theorem mu_one (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (r : ℝ) : SourceGeneralMaxwell.mu d r=1 := by
  rw [← SourceGeneralMaxwell.dispersion_identity,SourceRadialSystem.dispersion_identity d hdisp]

theorem tm_dielectric_weak (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian p=0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) (h0 : 0∉tsupport φ) :
    weakCurlPairing (SourceUnclippedMaxwell.electric d p) φ=(fun i => ∫ x,
      (Complex.I*SourceUnclippedMaxwell.magnetic d p x i)*φ x) ∧
    weakCurlPairing (SourceUnclippedMaxwell.magnetic d p) φ=(fun i => ∫ x,
      (-Complex.I*sigma d ‖x‖*SourceUnclippedMaxwell.electric d p x i)*φ x) :=
  ⟨SourceUnclippedMaxwell.first_weak_maxwell d hdisp p φ hφ hcompact h0,
    SourceUnclippedMaxwell.second_weak_maxwell d p hp hh φ (hφ.of_le (by norm_num)) hcompact h0⟩

theorem te_dielectric_weak (d : Data) (hσ : ∀ g∈d.gs,g.σ=1)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian p=0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) (h0 : 0∉tsupport φ) :
    weakCurlPairing (SourceGeneralMaxwell.teElectric d p) φ=(fun i => ∫ x,
      (Complex.I*SourceGeneralMaxwell.teMagnetic d p x i)*φ x) ∧
    weakCurlPairing (SourceGeneralMaxwell.teMagnetic d p) φ=(fun i => ∫ x,
      (-Complex.I*SourceGeneralMaxwell.mu d ‖x‖*SourceGeneralMaxwell.teElectric d p x i)*φ x) := by
  refine ⟨?_,SourceGeneralMaxwell.te_second_weak_maxwell d p φ hφ hcompact h0⟩
  simpa only [sigma_one d hσ,mul_one] using
    SourceGeneralMaxwell.te_first_weak_maxwell d p hp hh φ (hφ.of_le (by norm_num)) hcompact h0

end OQ14.SourceDielectricMaxwell

#print axioms OQ14.SourceDielectricMaxwell.sigma_one
#print axioms OQ14.SourceDielectricMaxwell.mu_one
#print axioms OQ14.SourceDielectricMaxwell.tm_dielectric_weak
#print axioms OQ14.SourceDielectricMaxwell.te_dielectric_weak
