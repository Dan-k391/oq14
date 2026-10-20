import RadialRellich
import RadialMoment

/-! # From actual spherical flux identities to the radial Rellich conclusion -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialMomentODE

open Complex Filter Set OQ14.RadialRellich OQ14.RadialMoment OQ14.Maxwell
  OQ14.AngularPower
open scoped Topology

def riccati (U : ℝ → ℂ) (r : ℝ) : ℂ := (r : ℂ)*U r

def riccatiD (U F : ℝ → ℂ) (r : ℝ) : ℂ := U r+F r/(r : ℂ)

theorem riccati_hasDerivAt (U F : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0)
    (hU : HasDerivAt U (F r/(r : ℂ)^2) r) :
    HasDerivAt (riccati U) (riccatiD U F r) r := by
  have hd : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
    simpa using (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt
  convert hd.mul hU using 1
  dsimp [riccatiD]
  field_simp [ofReal_ne_zero.mpr hr]
  ring

theorem riccatiD_hasDerivAt (l : ℕ) (k : ℂ) (U F : ℝ → ℂ) (r : ℝ) (hr : r ≠ 0)
    (hU : HasDerivAt U (F r/(r : ℂ)^2) r)
    (hF : HasDerivAt F (((l : ℂ)*(l+1)-k^2*(r : ℂ)^2)*U r) r) :
    HasDerivAt (riccatiD U F) (radialCoefficient l k r*riccati U r) r := by
  have hd : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 r := by
    simpa using (Complex.ofRealCLM.hasFDerivAt (x := r)).hasDerivAt
  convert hU.add (hF.div hd (ofReal_ne_zero.mpr hr)) using 1
  dsimp [radialCoefficient, riccati]
  field_simp [ofReal_ne_zero.mpr hr]
  ring

theorem flux_zero_of_tendsto (l : ℕ) (k : ℝ) (hk : 0 < k)
    (R : ℝ) (hR : 0 ≤ R) (U F : ℝ → ℂ)
    (hU : ∀ r, R < r → HasDerivAt U (F r/(r : ℂ)^2) r)
    (hF : ∀ r, R < r → HasDerivAt F
      (((l : ℂ)*(l+1)-(k : ℂ)^2*(r : ℂ)^2)*U r) r)
    (hlimit : Tendsto (riccati U) atTop (𝓝 0)) :
    ∀ r, R < r → U r = 0 := by
  have hz := radial_ode_zero_of_tendsto l k hk R hR (riccati U) (riccatiD U F)
    (fun r hr => riccati_hasDerivAt U F r (ne_of_gt (lt_of_le_of_lt hR hr)) (hU r hr))
    (fun r hr => riccatiD_hasDerivAt l (k : ℂ) U F r
      (ne_of_gt (lt_of_le_of_lt hR hr)) (hU r hr) (hF r hr)) hlimit
  intro r hr
  exact (mul_eq_zero.mp (hz r hr)).resolve_left
    (ofReal_ne_zero.mpr (ne_of_gt (lt_of_le_of_lt hR hr)))

theorem moment_zero_of_flux (l : ℕ) (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u {x : Space | R < ‖x‖})
    (P : Sphere → ℂ) (hP : Continuous P) (F : ℝ → ℂ)
    (hflux : ∀ r, R < r → momentD u P r = F r/(r : ℂ)^2)
    (hF : ∀ r, R < r → HasDerivAt F
      (((l : ℂ)*(l+1)-(k : ℂ)^2*(r : ℂ)^2)*moment u P r) r)
    (hmass : Tendsto (sphericalMass u) atTop (𝓝 0)) :
    ∀ r, R < r → moment u P r = 0 := by
  exact flux_zero_of_tendsto l k hk R hR (moment u P) F
    (fun r hr => (hflux r hr) ▸ moment_hasDerivAt R r hR hr u hu P hP)
    hF (radius_moment_tendsto_zero R hR u hu.continuousOn P hP hmass)

end OQ14.RadialMomentODE

#print axioms OQ14.RadialMomentODE.riccati_hasDerivAt
#print axioms OQ14.RadialMomentODE.riccatiD_hasDerivAt
#print axioms OQ14.RadialMomentODE.flux_zero_of_tendsto
#print axioms OQ14.RadialMomentODE.moment_zero_of_flux
