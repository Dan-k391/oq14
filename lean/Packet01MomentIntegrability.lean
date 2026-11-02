import HarmonicMomentIntegrability

noncomputable section
set_option autoImplicit false
namespace OQ14.Packet01MomentIntegrability
open Complex MeasureTheory Set OQ14.Maxwell OQ14.AngularPower
  OQ14.SphericalMomentEquation OQ14.HarmonicPolynomial OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability
open scoped Topology

theorem moment_locallyIntegrableOn (f : ScalarL2) (σ : Sphere → ℂ)
    (hσ : Measurable σ) (hσlp : MemLp σ 2 angularMeasure) :
    LocallyIntegrableOn (moment f σ) (Ioi (0 : ℝ)) := by
  have hw : LocallyIntegrableOn (fun r : ℝ => (r : ℂ) * moment f σ r) (Ioi (0 : ℝ)) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict
      ((radial_moment_memLp f σ hσ hσlp).locallyIntegrable (by norm_num))
  have hinv : ContinuousOn (fun r : ℝ => (r : ℂ)⁻¹) (Ioi (0 : ℝ)) := by
    apply ContinuousOn.inv₀ Complex.continuous_ofReal.continuousOn
    intro r hr
    exact_mod_cast (ne_of_gt hr)
  have h := hw.continuousOn_mul hinv isOpen_Ioi.isLocallyClosed
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed] at h ⊢
  intro K hK hKc
  apply (h K hK hKc).congr_fun
  intro r hr
  have hn : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (hK hr))
  simp [hn, mul_assoc]
  exact hKc.measurableSet
theorem radialMoment_locallyIntegrableOn (E : Fin 3 → ScalarL2) (p : Poly) :
    LocallyIntegrableOn (radialMoment E p) (Ioi (0 : ℝ)) := by
  have hi (j : Fin 3) := moment_locallyIntegrableOn (E j) (radialWeight p j)
    (radial_weight_continuous p j).measurable (weight_memLp p j).1
  have he : radialMoment E p = moment (E 0) (radialWeight p 0) +
      moment (E 1) (radialWeight p 1) + moment (E 2) (radialWeight p 2) := by
    ext r
    simp [radialMoment, Fin.sum_univ_three]
  rw [he]
  exact ((hi 0).add (hi 1)).add (hi 2)

theorem gradientMoment_locallyIntegrableOn (E : Fin 3 → ScalarL2) (p : Poly) :
    LocallyIntegrableOn (gradientMoment E p) (Ioi (0 : ℝ)) := by
  have hi (j : Fin 3) := moment_locallyIntegrableOn (E j) (gradientWeight p j)
    (angularPolynomial_continuous _).measurable (weight_memLp p j).2
  have he : gradientMoment E p = moment (E 0) (gradientWeight p 0) +
      moment (E 1) (gradientWeight p 1) + moment (E 2) (gradientWeight p 2) := by
    ext r
    simp [gradientMoment, Fin.sum_univ_three]
  rw [he]
  exact ((hi 0).add (hi 1)).add (hi 2)

theorem tangentialMoment_locallyIntegrableOn (E : Fin 3 → ScalarL2) (p : Poly) (l : ℕ) :
    LocallyIntegrableOn (tangentialMoment E p l) (Ioi (0 : ℝ)) := by
  exact (gradientMoment_locallyIntegrableOn E p).sub
    ((radialMoment_locallyIntegrableOn E p).continuousOn_mul continuousOn_const isOpen_Ioi.isLocallyClosed)

theorem weighted_tangentialMoment_locallyIntegrableOn (E : Fin 3 → ScalarL2) (p : Poly) (l : ℕ) :
    LocallyIntegrableOn (fun r : ℝ => (r : ℂ) * tangentialMoment E p l r) (Ioi (0 : ℝ)) := by
  exact (tangentialMoment_locallyIntegrableOn E p l).continuousOn_mul
    Complex.continuous_ofReal.continuousOn isOpen_Ioi.isLocallyClosed

#print axioms OQ14.Packet01MomentIntegrability.moment_locallyIntegrableOn
#print axioms OQ14.Packet01MomentIntegrability.radialMoment_locallyIntegrableOn
#print axioms OQ14.Packet01MomentIntegrability.gradientMoment_locallyIntegrableOn
#print axioms OQ14.Packet01MomentIntegrability.tangentialMoment_locallyIntegrableOn
#print axioms OQ14.Packet01MomentIntegrability.weighted_tangentialMoment_locallyIntegrableOn
end OQ14.Packet01MomentIntegrability
