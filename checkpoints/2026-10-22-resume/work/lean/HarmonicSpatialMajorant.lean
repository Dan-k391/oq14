import RiccatiImaginaryBound
import NormalizedHarmonicJets

/-! Actual normalized solid-wave jet envelopes suitable for the radial majorants. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.HarmonicSpatialMajorant
open OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.NormalizedHarmonicJets
  OQ14.SolidSpatialBounds OQ14.RiccatiSeriesCoefficients

def angularScale : ℝ := 2*(4*Real.exp 1)^3
def areaScale : ℝ := 1+(angularMeasure.real Set.univ)⁻¹

theorem angular_exponential_identity (l : ℕ) :
    2^l*(4^l*Real.exp (((l+1 : ℕ) : ℝ)))^3=(Real.exp 1)^3*angularScale^l := by
  have he : Real.exp (((l+1 : ℕ) : ℝ))=(Real.exp 1)^(l+1) := by
    simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) (l+1)
  rw [he,pow_succ]
  simp only [angularScale,mul_pow,← pow_mul]
  ring

theorem coefficient_exponential_bound (l : ℕ) :
    coefficientEnvelope l ≤ areaScale*(Real.exp 1)^3*(l+1 : ℝ)^3*angularScale^l := by
  refine (coefficientEnvelope_polynomial_bound l).trans_eq ?_
  calc
    _ = (1+(angularMeasure.real Set.univ)⁻¹)*(((l+1)^3 : ℕ) : ℝ)*
        (2^l*(4^l*Real.exp (((l+1 : ℕ) : ℝ)))^3) := by ring
    _ = _ := by
      rw [angular_exponential_identity]
      simp only [areaScale,Nat.cast_pow,Nat.cast_add,Nat.cast_one]
      ring

def degreeScale (N : ℕ) (b : ℝ) : ℝ := angularScale*(2^N*max 1 b)
def jetScale (q : ℂ) (N : ℕ) (b : ℝ) : ℝ :=
  2^N*((N.factorial : ℝ)*Real.exp (‖q^2‖*b^2/2)*compositionScale q N b^N)*
    (((N : ℝ)+1)*areaScale*(Real.exp 1)^3*(2^N)^2)

theorem jetScale_nonnegative (q : ℂ) (N : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    0 ≤ jetScale q N b := by
  have hD : 0 ≤ compositionScale q N b := (zero_le_one.trans (compositionScale_ge_one q N b hb))
  have harea : 0 ≤ areaScale := by dsimp [areaScale]; positivity
  dsimp [jetScale]
  positivity

theorem normalized_wave_jet_bound (l : ℕ) (i : Index l) (q : ℂ)
    (N : ℕ) (b : ℝ) (hb : 0 ≤ b) (x : Space) (hx : ‖x‖ ≤ b) :
    ‖iteratedFDeriv ℝ N (SolidScalarHelmholtz.wave l q (representative l i)) x‖ ≤
      jetScale q N b*amplitude l 0*(l+1 : ℝ)^3*degreeScale N b^l := by
  refine (normalized_solid_wave_bound l i q N b hb x hx).trans ?_
  have hD : 0 ≤ compositionScale q N b := zero_le_one.trans (compositionScale_ge_one q N b hb)
  have hA := (amplitude_pos l 0).le
  calc
    _ ≤ 2^N*((N.factorial : ℝ)*(amplitude l 0*Real.exp (‖q^2‖*b^2/2))*compositionScale q N b^N)*
        (((N : ℝ)+1)*(areaScale*(Real.exp 1)^3*(l+1 : ℝ)^3*angularScale^l)*(2^N)^2*(2^N*max 1 b)^l) := by
      gcongr
      exact coefficient_exponential_bound l
    _ = _ := by simp only [jetScale,degreeScale,mul_pow]; ring


theorem degreeScale_nonnegative (N : ℕ) (b : ℝ) : 0 ≤ degreeScale N b := by
  dsimp [degreeScale,angularScale]
  positivity

end OQ14.HarmonicSpatialMajorant

#print axioms OQ14.HarmonicSpatialMajorant.angular_exponential_identity

#print axioms OQ14.HarmonicSpatialMajorant.coefficient_exponential_bound

#print axioms OQ14.HarmonicSpatialMajorant.jetScale_nonnegative

#print axioms OQ14.HarmonicSpatialMajorant.normalized_wave_jet_bound

#print axioms OQ14.HarmonicSpatialMajorant.degreeScale_nonnegative
