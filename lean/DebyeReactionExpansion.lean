import PlaneDebyeCoefficients

/-! The existing physical reaction tensor as an actual convergent regular Debye series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.DebyeReactionExpansion
open OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.PlaneDebyeCoefficients OQ14.TransversePlaneFields
open scoped ComplexInnerProductSpace

def coefficient (k : ℝ) (x : Space) (i : Fin 3) : ComplexTransverseExpansion.ModeIndex → ℂ :=
  Sum.elim
    (fun a => (normalizer a.1 : ℂ)*(phaseCoefficient (a.1+1) k/(Complex.I*(-(k : ℂ))))*
      DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave (a.1+1) (-k) (representative (a.1+1) a.2)) x i)
    (fun a => (normalizer a.1 : ℂ)*phaseCoefficient (a.1+1) k*
      DebyeCalculus.toroidal (SolidScalarHelmholtz.wave (a.1+1) (-k) (representative (a.1+1) a.2)) x i)

theorem actual_coefficient (k : ℝ) (hk : k≠0) (x : Space) (i : Fin 3)
    (a : ComplexTransverseExpansion.ModeIndex) :
    ⟪ComplexTransverseExpansion.vector a,field k x i⟫=coefficient k x i a := by
  cases a with
  | inl a => exact normalized_poloidal a k hk x i
  | inr a => exact normalized_toroidal a k x i

theorem J_expansion (k : ℝ) (hk : k≠0) (x y : Space) (i j : Fin 3) :
    HasSum (fun a : ComplexTransverseExpansion.ModeIndex =>
      (((k^3/(16*Real.pi^2) : ℝ) : ℂ)*
        ((starRingEnd ℂ) (coefficient k x i a)*coefficient k y j a)))
      (SphereReactionKernel.J k (x-y) i j) := by
  convert J_series k x y i j using 1
  funext a
  rw [← actual_coefficient k hk x i a,← actual_coefficient k hk y j a,inner_conj_symm]

end OQ14.DebyeReactionExpansion

#print axioms OQ14.DebyeReactionExpansion.actual_coefficient
#print axioms OQ14.DebyeReactionExpansion.J_expansion
