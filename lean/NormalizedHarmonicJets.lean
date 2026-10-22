import PolynomialTensorInterpolation
import SphereHarmonicAddition
import SphereHarmonicDimension

/-! Actual coefficient and compact derivative bounds for the constructed normalized harmonics. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.NormalizedHarmonicJets

open OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis OQ14.SphereHarmonicAddition
  OQ14.PolynomialJetBounds OQ14.PolynomialTensorInterpolation OQ14.SolidSpatialBounds

def rankEnvelope (l : ℕ) : ℝ :=
  Real.sqrt (((l+1)^3 : ℕ)/angularMeasure.real Set.univ)

theorem angular_bound (l : ℕ) (i : Index l) (n : Sphere) : ‖angular l i n‖ ≤ rankEnvelope l := by
  refine (angular_norm_bound l i n).trans (Real.sqrt_le_sqrt ?_)
  exact div_le_div_of_nonneg_right (by exact_mod_cast SphereHarmonicDimension.harmonicSpace_finrank_le l)
    area_pos.le

theorem radius_unit_representation (x : Space) :
    ∃ (r : ℝ) (n : Sphere),0 ≤ r ∧ r=‖x‖ ∧ x=r • (n : Space) := by
  by_cases hx : x=0
  · subst x
    let n : Sphere := ⟨Maxwell.basis 0,by simp [Maxwell.basis,Metric.mem_sphere]⟩
    exact ⟨0,n,le_rfl,by simp,by simp⟩
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hu : ‖‖x‖⁻¹ • x‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ hn]
    let n : Sphere := ⟨‖x‖⁻¹ • x,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩
    refine ⟨‖x‖,n,norm_nonneg _,rfl,?_⟩
    change x=‖x‖ • (‖x‖⁻¹ • x)
    rw [smul_smul,mul_inv_cancel₀ hn,one_smul]

theorem representative_point_bound (l : ℕ) (i : Index l) (B : ℝ) (hB : 0 ≤ B)
    (x : Space) (hx : ‖x‖ ≤ B) :
    ‖evaluate (representative l i) x‖ ≤ B^l*rankEnvelope l := by
  obtain ⟨r,n,hr,heq,hrep⟩ := radius_unit_representation x
  have hrB : r ≤ B := heq.trans_le hx
  have hang : ‖evaluate (representative l i) (n : Space)‖ ≤ rankEnvelope l := by
    simpa only [angular,SpherePolynomial.polynomialMap_apply,evaluate] using angular_bound l i n
  rw [hrep,FischerDecomposition.evaluate_smul _ l (representative_homogeneous l i),
    norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg hr]
  exact mul_le_mul (pow_le_pow_left₀ hr hrB l) hang (norm_nonneg _) (pow_nonneg hB _)

def coefficientEnvelope (l : ℕ) : ℝ :=
  2^l*rankEnvelope l*(4^l*Real.exp (((l+1 : ℕ) : ℝ)))^3

theorem coefficientEnvelope_nonneg (l : ℕ) : 0 ≤ coefficientEnvelope l := by
  unfold coefficientEnvelope rankEnvelope
  positivity

theorem representative_coefficient_bound (l : ℕ) (i : Index l) :
    coefficientNorm (representative l i) ≤ coefficientEnvelope l := by
  apply coefficient_exp_bound_of_grid l (representative l i)
  · exact (MvPolynomial.restrictTotalDegree_le_restrictDegree (Fin 3) ℝ l)
      (harmonicPolynomials_le_totalDegree l (representative l i).property)
  · exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  · intro a b c
    exact representative_point_bound l i 2 (by norm_num) _ (gridPoint_norm_le_two l a b c)

theorem representative_compact_jet_bound (l : ℕ) (i : Index l) (N : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    jetNorm (complexEvaluate (representative l i)) N b ≤
      ((N : ℝ)+1)*coefficientEnvelope l*(2^N)^2*(2^N*max 1 b)^l := by
  refine (homogeneous_compact_jet_bound _ l (representative_homogeneous l i) N b hb).trans ?_
  gcongr
  exact representative_coefficient_bound l i

theorem normalized_solid_wave_bound (l : ℕ) (i : Index l) (q : ℂ)
    (N : ℕ) (b : ℝ) (hb : 0 ≤ b) (x : Space) (hx : ‖x‖ ≤ b) :
    ‖iteratedFDeriv ℝ N (SolidScalarHelmholtz.wave l q (representative l i)) x‖ ≤
      2^N*((N.factorial : ℝ)*(RiccatiSeriesCoefficients.amplitude l 0*
        Real.exp (‖q^2‖*b^2/2))*compositionScale q N b^N)*
        (((N : ℝ)+1)*coefficientEnvelope l*(2^N)^2*(2^N*max 1 b)^l) := by
  refine (solid_wave_coefficient_bound _ l (representative_homogeneous l i) q N b hb x hx).trans ?_
  have ha := (RiccatiSeriesCoefficients.amplitude_pos l 0).le
  have hD := (compositionScale_ge_one q N b hb).trans' (by norm_num : (0 : ℝ) ≤ 1)
  gcongr
  exact representative_coefficient_bound l i

theorem rankEnvelope_polynomial_bound (l : ℕ) :
    rankEnvelope l ≤ (1+(angularMeasure.real Set.univ)⁻¹)*(((l+1)^3 : ℕ) : ℝ) := by
  let y : ℝ := (((l+1)^3 : ℕ) : ℝ)
  let t : ℝ := y/angularMeasure.real Set.univ
  have hy : 1 ≤ y := by dsimp [y]; exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 3 (Nat.succ_ne_zero l)))
  have ht : 0 ≤ t := div_nonneg (by dsimp [y]; positivity) area_pos.le
  have hs := Real.sq_sqrt ht
  have hsq := sq_nonneg (Real.sqrt t-1)
  change Real.sqrt t ≤ (1+(angularMeasure.real Set.univ)⁻¹)*y
  calc
    _ ≤ t+1 := by nlinarith [Real.sqrt_nonneg t]
    _ ≤ t+y := add_le_add_left hy _
    _ = _ := by dsimp [t]; ring

theorem coefficientEnvelope_polynomial_bound (l : ℕ) :
    coefficientEnvelope l ≤ (1+(angularMeasure.real Set.univ)⁻¹)*(((l+1)^3 : ℕ) : ℝ)*
      2^l*(4^l*Real.exp (((l+1 : ℕ) : ℝ)))^3 := by
  calc
    _ ≤ 2^l*((1+(angularMeasure.real Set.univ)⁻¹)*(((l+1)^3 : ℕ) : ℝ))*
        (4^l*Real.exp (((l+1 : ℕ) : ℝ)))^3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (rankEnvelope_polynomial_bound l) (by positivity)
    _ = _ := by ring

end OQ14.NormalizedHarmonicJets

#print axioms OQ14.NormalizedHarmonicJets.angular_bound
#print axioms OQ14.NormalizedHarmonicJets.radius_unit_representation
#print axioms OQ14.NormalizedHarmonicJets.representative_point_bound
#print axioms OQ14.NormalizedHarmonicJets.coefficientEnvelope_nonneg
#print axioms OQ14.NormalizedHarmonicJets.representative_coefficient_bound
#print axioms OQ14.NormalizedHarmonicJets.representative_compact_jet_bound
#print axioms OQ14.NormalizedHarmonicJets.normalized_solid_wave_bound
#print axioms OQ14.NormalizedHarmonicJets.rankEnvelope_polynomial_bound
#print axioms OQ14.NormalizedHarmonicJets.coefficientEnvelope_polynomial_bound
