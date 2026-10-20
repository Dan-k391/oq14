import SphereAngularSymmetry
import VectorFourier
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Actual radius--latitude--azimuth coordinates in three-dimensional Euclidean volume.
Indices 0 and 1 are transverse; index 2 is the axial coordinate. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000

namespace OQ14.AxialCoordinates
open MeasureTheory Set Real Matrix OQ14.Maxwell OQ14.AngularPower
open scoped Topology ENNReal

abbrev Coordinates := Fin 3 → ℝ

def domain : Set Coordinates := {p | 0 < p 0 ∧ p 1 ∈ Ioo (-1 : ℝ) 1 ∧ p 2 ∈ Ioo (-Real.pi) Real.pi}
def transverse (z : ℝ) : ℝ := Real.sqrt (1-z^2)
def map (p : Coordinates) : Coordinates :=
  ![p 0*transverse (p 1)*Real.cos (p 2),
    p 0*transverse (p 1)*Real.sin (p 2), p 0*p 1]
def physical (p : Coordinates) : Space := (WithLp.equiv 2 Coordinates).symm (map p)

theorem transverse_pos (z : ℝ) (hz : z ∈ Ioo (-1 : ℝ) 1) : 0 < transverse z := by
  apply Real.sqrt_pos.mpr
  nlinarith [hz.1,hz.2]

theorem transverse_sq (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) : transverse z^2 = 1-z^2 := by
  apply Real.sq_sqrt
  nlinarith [hz.1,hz.2]

theorem physical_norm (p : Coordinates) (hp : p ∈ domain) : ‖physical p‖ = p 0 := by
  have hn : ‖physical p‖^2 = (p 0)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [physical, map, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    change (p 0*transverse (p 1)*cos (p 2))^2 +
      (p 0*transverse (p 1)*sin (p 2))^2 + (p 0*p 1)^2 = (p 0)^2
    linear_combination (p 0)^2*(transverse (p 1))^2*(Real.cos_sq_add_sin_sq (p 2)) +
      (p 0)^2*(transverse_sq (p 1) ⟨hp.2.1.1.le,hp.2.1.2.le⟩)
  exact (sq_eq_sq₀ (norm_nonneg _) hp.1.le).mp hn

def jacobianMatrix (p : Coordinates) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![transverse (p 1)*Real.cos (p 2), -(p 0*p 1/transverse (p 1))*Real.cos (p 2), -p 0*transverse (p 1)*Real.sin (p 2);
     transverse (p 1)*Real.sin (p 2), -(p 0*p 1/transverse (p 1))*Real.sin (p 2), p 0*transverse (p 1)*Real.cos (p 2);
     p 1, p 0, 0]

def derivative (p : Coordinates) : Coordinates →L[ℝ] Coordinates :=
  (Matrix.toLin' (jacobianMatrix p)).toContinuousLinearMap

theorem derivative_apply (p v : Coordinates) :
    derivative p v = (jacobianMatrix p).mulVec v := rfl

theorem map_hasFDerivAt (p : Coordinates) (hp : p ∈ domain) : HasFDerivAt map (derivative p) p := by
  have ht : HasFDerivAt (𝕜 := ℝ) (fun q : Coordinates => transverse (q 1))
      ((-(p 1)/transverse (p 1)) • ContinuousLinearMap.proj 1) p := by
    have hd : HasDerivAt transverse (-(p 1)/transverse (p 1)) (p 1) := by
      have h := (((hasDerivAt_id (p 1)).pow 2).const_sub 1).sqrt
        (by have h := transverse_pos (p 1) hp.2.1; exact (Real.sqrt_pos.mp h).ne')
      convert h using 1
      dsimp only [transverse, id_eq]
      norm_num
      ring
    exact hd.comp_hasFDerivAt (h₂ := transverse) (f := fun q : Coordinates => q 1)
      p (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hc := (Real.hasDerivAt_cos (p 2)).comp_hasFDerivAt p (hasFDerivAt_apply (𝕜 := ℝ) 2 p)
  have hs := (Real.hasDerivAt_sin (p 2)).comp_hasFDerivAt p (hasFDerivAt_apply (𝕜 := ℝ) 2 p)
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · convert ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).mul ht).mul hc using 1
    ext v
    simp [map, derivative_apply, jacobianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      ContinuousLinearMap.comp_apply, mul_comm, mul_left_comm, mul_assoc]
    ring
  · convert ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).mul ht).mul hs using 1
    ext v
    simp [map, derivative_apply, jacobianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      ContinuousLinearMap.comp_apply, mul_comm, mul_left_comm, mul_assoc]
    ring
  · convert (hasFDerivAt_apply (𝕜 := ℝ) 0 p).mul (hasFDerivAt_apply (𝕜 := ℝ) 1 p) using 1
    ext v
    simp [map, derivative_apply, jacobianMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      ContinuousLinearMap.comp_apply]
    ring

theorem derivative_det (p : Coordinates) (hp : p ∈ domain) : (derivative p).det = -(p 0)^2 := by
  rw [derivative, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin']
  have ht := transverse_pos (p 1) hp.2.1
  have hs := transverse_sq (p 1) ⟨hp.2.1.1.le,hp.2.1.2.le⟩
  simp [jacobianMatrix, Matrix.det_fin_three]
  field_simp [ht.ne']
  linear_combination -(p 0)^2*transverse (p 1)*(Real.cos_sq_add_sin_sq (p 2)) -
    (p 0)^2*transverse (p 1)*(cos (p 2)^2+sin (p 2)^2)*hs

theorem recover_polar (p : Coordinates) (hp : p ∈ domain) :
    polarCoord (map p 0, map p 1) = (p 0*transverse (p 1), p 2) := by
  have h : (p 0*transverse (p 1),p 2) ∈ polarCoord.target :=
    ⟨mul_pos hp.1 (transverse_pos (p 1) hp.2.1), hp.2.2⟩
  change polarCoord (polarCoord.symm (p 0*transverse (p 1),p 2)) = _
  exact polarCoord.right_inv h

theorem map_injective : InjOn map domain := by
  intro p hp q hq he
  have hphys : physical p = physical q := congrArg (WithLp.equiv 2 Coordinates).symm he
  have hr : p 0 = q 0 := by rw [← physical_norm p hp, ← physical_norm q hq, hphys]
  have hz0 := congrFun he 2
  change p 0*p 1 = q 0*q 1 at hz0
  have hz : p 1 = q 1 := by rw [←hr] at hz0; exact mul_left_cancel₀ hp.1.ne' hz0
  have hxy : (map p 0,map p 1) = (map q 0,map q 1) :=
    Prod.ext (congrFun he 0) (congrFun he 1)
  have hθ := congrArg Prod.snd (congrArg polarCoord hxy)
  rw [recover_polar p hp,recover_polar q hq] at hθ
  funext i
  fin_cases i
  · exact hr
  · exact hz
  · exact hθ

theorem domain_open : IsOpen domain := by
  apply IsOpen.inter (isOpen_lt continuous_const (continuous_apply 0))
  exact (isOpen_Ioo.preimage (continuous_apply 1)).inter
    (isOpen_Ioo.preimage (continuous_apply 2))

theorem image_contains_transverse (x : Coordinates) (hy : x 1 ≠ 0) : x ∈ map '' domain := by
  let r := ‖(WithLp.equiv 2 Coordinates).symm x‖
  let c := polarCoord (x 0,x 1)
  have hsrc : (x 0,x 1) ∈ polarCoord.source := Or.inr hy
  have hc : c ∈ polarCoord.target := polarCoord.map_source hsrc
  have hcpos : 0 < c.1 := hc.1
  have hrec : (c.1*cos c.2,c.1*sin c.2) = (x 0,x 1) := polarCoord.left_inv hsrc
  have hrsq : r^2 = (x 0)^2+(x 1)^2+(x 2)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp [r, Fin.sum_univ_three, Real.norm_eq_abs]
  have hcsq : c.1^2 = (x 0)^2+(x 1)^2 := by
    change (Real.sqrt ((x 0)^2+(x 1)^2))^2 = _
    exact Real.sq_sqrt (by positivity)
  have hr : 0 < r := by
    have hn : 0 ≤ r := norm_nonneg _
    nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (x 0),sq_nonneg (x 2)]
  have hz : x 2/r ∈ Ioo (-1 : ℝ) 1 := by
    have hx : |x 2| < r := by nlinarith [hcpos, sq_abs (x 2), abs_nonneg (x 2)]
    apply abs_lt.mp
    rw [abs_div, abs_of_pos hr]
    exact (div_lt_one hr).mpr hx
  have hρ : r*transverse (x 2/r) = c.1 := by
    apply (sq_eq_sq₀ (mul_nonneg hr.le (transverse_pos _ hz).le) hcpos.le).mp
    rw [mul_pow,transverse_sq _ ⟨hz.1.le,hz.2.le⟩,div_pow]
    field_simp
    nlinarith [hrsq,hcsq]
  refine ⟨![r,x 2/r,c.2], ?_, ?_⟩
  · exact ⟨hr,hz,hc.2⟩
  · funext i
    fin_cases i
    · change r*transverse (x 2/r)*cos c.2=x 0
      rw [hρ]
      exact congrArg Prod.fst hrec
    · change r*transverse (x 2/r)*sin c.2=x 1
      rw [hρ]
      exact congrArg Prod.snd hrec
    · change r*(x 2/r)=x 2
      field_simp

theorem image_ae_eq_univ : map '' domain =ᵐ[volume] (univ : Set Coordinates) := by
  have hsub : (map '' domain)ᶜ ⊆ LinearMap.ker (LinearMap.proj (R := ℝ) 1 : Coordinates →ₗ[ℝ] ℝ) := by
    intro x hx
    change x 1 = 0
    by_contra hy
    exact hx (image_contains_transverse x hy)
  have hzero : volume (LinearMap.ker (LinearMap.proj (R := ℝ) 1 : Coordinates →ₗ[ℝ] ℝ) : Set Coordinates) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    have he := LinearMap.congr_fun h (![0,1,0] : Coordinates)
    norm_num at he
  simp only [ae_eq_univ]
  exact le_antisymm ((measure_mono hsub).trans (le_of_eq hzero)) bot_le

theorem lintegral_coordinates (f : Coordinates → ℝ≥0∞) :
    (∫⁻ x, f x) = ∫⁻ p in domain, ENNReal.ofReal ((p 0)^2)*f (map p) := by
  calc
    _ = ∫⁻ x in map '' domain, f x := by
      rw [← setLIntegral_univ, setLIntegral_congr image_ae_eq_univ.symm]
    _ = _ := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume domain_open.measurableSet
        (fun p hp => (map_hasFDerivAt p hp).hasFDerivWithinAt) map_injective]
      apply setLIntegral_congr_fun domain_open.measurableSet
      filter_upwards with p hp
      rw [derivative_det p hp, abs_neg, abs_of_nonneg (sq_nonneg _)]

theorem integral_coordinates (f : Coordinates → ℝ) :
    (∫ x, f x) = ∫ p in domain, (p 0)^2*f (map p) := by
  calc
    _ = ∫ x in map '' domain, f x := by
      rw [← setIntegral_univ]
      exact setIntegral_congr_set image_ae_eq_univ.symm
    _ = _ := by
      rw [integral_image_eq_integral_abs_det_fderiv_smul volume domain_open.measurableSet
        (fun p hp => (map_hasFDerivAt p hp).hasFDerivWithinAt) map_injective]
      apply setIntegral_congr_fun domain_open.measurableSet
      intro p hp
      dsimp only
      rw [derivative_det p hp, abs_neg, abs_of_nonneg (sq_nonneg _), smul_eq_mul]

end OQ14.AxialCoordinates

#print axioms OQ14.AxialCoordinates.transverse_pos
#print axioms OQ14.AxialCoordinates.transverse_sq
#print axioms OQ14.AxialCoordinates.physical_norm
#print axioms OQ14.AxialCoordinates.derivative_apply
#print axioms OQ14.AxialCoordinates.map_hasFDerivAt
#print axioms OQ14.AxialCoordinates.derivative_det
#print axioms OQ14.AxialCoordinates.recover_polar
#print axioms OQ14.AxialCoordinates.map_injective
#print axioms OQ14.AxialCoordinates.domain_open
#print axioms OQ14.AxialCoordinates.image_contains_transverse
#print axioms OQ14.AxialCoordinates.image_ae_eq_univ
#print axioms OQ14.AxialCoordinates.lintegral_coordinates
#print axioms OQ14.AxialCoordinates.integral_coordinates
