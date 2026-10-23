import RestrictedTEFields

/-! Exact electric-wall and partner-point parities of actual restricted TE sums. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEParity
open Maxwell RestrictedTEFields SphereReactionKernel
abbrev Space := FourierL2.Space

theorem electric_central (k : ℝ) (A : SymmetricHarmonicJets.Index →₀ ℂ) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teElectric (potential k A) (-x) i=DebyeMaxwell.teElectric (potential k A) x i := by
  have h := SolidWaveParity.curl_parity (DebyeCalculus.radialVector (potential k A))
    (fun j y => (DebyeCalculus.radialVector_smooth _ y (potential_smooth k A).contDiffAt j).differentiableAt (by simp))
    (-1) (by
      intro y j
      simp only [DebyeCalculus.radialVector,PiLp.neg_apply,Complex.ofReal_neg,potential_central_even]
      ring) x i
  simpa only [neg_neg,one_mul,DebyeMaxwell.teElectric,DebyeCalculus.toroidal] using h

theorem magnetic_central (k : ℝ) (A : SymmetricHarmonicJets.Index →₀ ℂ) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teMagnetic k (potential k A) (-x) i= -DebyeMaxwell.teMagnetic k (potential k A) x i := by
  have h := SolidWaveParity.curl_parity (DebyeMaxwell.teElectric (potential k A))
    (fun j y => (DebyeCalculus.toroidal_smooth _ y (potential_smooth k A).contDiffAt j).differentiableAt (by simp))
    1 (fun y j => by simpa only [one_mul] using electric_central k A y j) x i
  change (-Complex.I/(k : ℂ))*curl (DebyeMaxwell.teElectric (potential k A)) (-x) i=_
  rw [h]
  simp only [one_mul,DebyeMaxwell.teMagnetic,DebyeMaxwell.teElectric]
  ring

theorem electric_wall (k : ℝ) (A : SymmetricHarmonicJets.Index →₀ ℂ) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teElectric (potential k A) (reflect x) i=
      -(sign i : ℂ)*DebyeMaxwell.teElectric (potential k A) x i := by
  have h := electric_half_turn k A x i
  rw [HalfTurnMaxwellParity.halfTurn_apply,electric_central] at h
  exact h

theorem magnetic_wall (k : ℝ) (A : SymmetricHarmonicJets.Index →₀ ℂ) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teMagnetic k (potential k A) (reflect x) i=
      (sign i : ℂ)*DebyeMaxwell.teMagnetic k (potential k A) x i := by
  have h := HalfTurnMaxwellParity.curl_invariant (DebyeMaxwell.teElectric (potential k A))
    (fun j y => (DebyeCalculus.toroidal_smooth _ y (potential_smooth k A).contDiffAt j).differentiableAt (by simp))
    (electric_half_turn k A) x i
  have hc : DebyeMaxwell.teMagnetic k (potential k A) (HalfTurnMaxwellParity.halfTurn x) i=
      -(sign i : ℂ)*DebyeMaxwell.teMagnetic k (potential k A) x i := by
    change (-Complex.I/(k : ℂ))*curl (DebyeMaxwell.teElectric (potential k A)) (HalfTurnMaxwellParity.halfTurn x) i=_
    rw [h]
    dsimp [DebyeMaxwell.teMagnetic,DebyeMaxwell.teElectric]
    ring
  rw [HalfTurnMaxwellParity.halfTurn_apply,magnetic_central] at hc
  linear_combination -hc

end OQ14.RestrictedTEParity
#print axioms OQ14.RestrictedTEParity.electric_central
#print axioms OQ14.RestrictedTEParity.magnetic_central
#print axioms OQ14.RestrictedTEParity.electric_wall
#print axioms OQ14.RestrictedTEParity.magnetic_wall
