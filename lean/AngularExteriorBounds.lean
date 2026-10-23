import HarmonicSpatialMajorant
import HarmonicRadiationFactors

/-! Actual normalized homogeneous angular fields have explicit exponential degree envelopes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.AngularExteriorBounds
open OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
open OQ14.HarmonicSpatialMajorant OQ14.NormalizedHarmonicJets OQ14.PolynomialJetBounds

def scale : ℝ := 4*areaScale*(Real.exp 1)^3
def base : ℝ := 2*angularScale
def envelope (l : ℕ) : ℝ := scale*(l+1 : ℝ)^3*base^l

theorem envelope_nonnegative (l : ℕ) : 0≤envelope l := by
  dsimp [envelope,scale,base,areaScale,angularScale]
  positivity

theorem scalar_derivative_bound (l : ℕ) (m : Index l) (n : Sphere) (i : Fin 3) :
    ‖dcoord (complexEvaluate (representative l m)) n i‖≤envelope l := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hp := homogeneous_jet_bound (representative l m) l (representative_homogeneous l m)
    1 1 (n : Space) 1 le_rfl hn.le le_rfl
  have hc := (representative_coefficient_bound l m).trans (coefficient_exponential_bound l)
  have hd : ‖dcoord (complexEvaluate (representative l m)) n i‖≤
      ‖iteratedFDeriv ℝ 1 (complexEvaluate (representative l m)) n‖ := by
    have he : ‖iteratedFDeriv ℝ 1 (complexEvaluate (representative l m)) n‖=
        ‖fderiv ℝ (complexEvaluate (representative l m)) n‖ := by
      simpa only [zero_add,norm_iteratedFDeriv_zero] using
        (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := complexEvaluate (representative l m)) (x := (n : Space))).symm
    rw [he]
    simpa only [dcoord,show ‖Maxwell.basis i‖=(1 : ℝ) by simp [Maxwell.basis],mul_one] using
      (fderiv ℝ (complexEvaluate (representative l m)) n).le_opNorm (Maxwell.basis i)
  refine (hd.trans hp).trans ?_
  calc
    _ ≤ (areaScale*(Real.exp 1)^3*(l+1 : ℝ)^3*angularScale^l)*(2^1)^2*(2^1*1)^l := by
      gcongr
    _ = _ := by simp only [envelope,scale,base,mul_pow];ring

theorem scalar_value_bound (l : ℕ) (m : Index l) (n : Sphere) :
    ‖complexEvaluate (representative l m) n‖≤envelope l := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hp := homogeneous_jet_bound (representative l m) l (representative_homogeneous l m)
    1 0 (n : Space) 1 le_rfl hn.le (by norm_num)
  rw [norm_iteratedFDeriv_zero] at hp
  have hc := (representative_coefficient_bound l m).trans (coefficient_exponential_bound l)
  refine hp.trans ?_
  calc
    _ ≤ (areaScale*(Real.exp 1)^3*(l+1 : ℝ)^3*angularScale^l)*(2^1)^2*(2^1*1)^l := by gcongr
    _ = _ := by simp only [envelope,scale,base,mul_pow];ring

theorem coordinate_bound (n : Sphere) (i : Fin 3) : ‖((n : Space) i : ℂ)‖≤1 := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  simpa only [Complex.norm_real,hn] using PiLp.norm_apply_le (n : Space) i

theorem radial_bound (l : ℕ) (m : Index l) (n : Sphere) (i : Fin 3) :
    ‖HarmonicRadiationFactors.radial (representative l m) n i‖≤envelope l := by
  rw [HarmonicRadiationFactors.radial,norm_mul]
  exact (mul_le_mul (coordinate_bound n i) (scalar_value_bound l m n)
    (norm_nonneg _) (by norm_num : (0 : ℝ)≤1)).trans_eq (one_mul _)

theorem toroidal_bound (l : ℕ) (m : Index l) (n : Sphere) (i : Fin 3) :
    ‖DebyeRadialTrace.angularToroidal (representative l m) n i‖≤2*envelope l := by
  have hb (a b : Fin 3) :
      ‖dcoord (complexEvaluate (representative l m)) n a*((n : Space) b : ℂ)‖≤envelope l := by
    rw [norm_mul]
    exact (mul_le_mul (scalar_derivative_bound l m n a) (coordinate_bound n b)
      (norm_nonneg _) (envelope_nonnegative l)).trans_eq (mul_one _)
  have hs (a b c d : Fin 3) :
      ‖dcoord (complexEvaluate (representative l m)) n a*((n : Space) b : ℂ)-
        dcoord (complexEvaluate (representative l m)) n c*((n : Space) d : ℂ)‖≤2*envelope l :=
    (norm_sub_le _ _).trans ((add_le_add (hb a b) (hb c d)).trans_eq (by ring))
  fin_cases i
  · exact hs 1 2 2 1
  · exact hs 2 0 0 2
  · exact hs 0 1 1 0

theorem poloidal_bound (l : ℕ) (m : Index l) (n : Sphere) (i : Fin 3) :
    ‖HarmonicRadiationFactors.poloidal (representative l m) n i‖≤(l+1 : ℝ)*envelope l := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  rw [HarmonicRadiationFactors.poloidal_formula _ l (representative_homogeneous l m),hn]
  simp only [Complex.ofReal_one,one_pow,one_mul]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,Complex.norm_natCast]
  exact (add_le_add (scalar_derivative_bound l m n i)
    (mul_le_mul_of_nonneg_left (radial_bound l m n i) (Nat.cast_nonneg l))).trans_eq (by ring)

end OQ14.AngularExteriorBounds

#print axioms OQ14.AngularExteriorBounds.envelope_nonnegative
#print axioms OQ14.AngularExteriorBounds.scalar_derivative_bound
#print axioms OQ14.AngularExteriorBounds.scalar_value_bound
#print axioms OQ14.AngularExteriorBounds.coordinate_bound
#print axioms OQ14.AngularExteriorBounds.radial_bound
#print axioms OQ14.AngularExteriorBounds.toroidal_bound
#print axioms OQ14.AngularExteriorBounds.poloidal_bound
