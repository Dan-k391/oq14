import MaxwellRadiation
import PlaneInverseCube

/-! # Actual bilinear normal-flux tails of compact Maxwell sources

The transverse leading terms cancel on the measurement plane. The actual
electric and magnetic response errors then give an integrable inverse-cube
bound, including cross terms between distinct compact source responses.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.MaxwellPlaneTail

open MeasureTheory Metric Set OQ14.Maxwell OQ14.MaxwellRadiation
  OQ14.ScalarRadiation OQ14.GreenKernel
open scoped Topology ComplexConjugate

theorem cross_norm_bound (u v : Vector) (A B : ℝ) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hu : ∀ i, ‖u i‖ ≤ A) (hv : ∀ i, ‖v i‖ ≤ B) (i : Fin 3) :
    ‖crossProduct u (conjugate v) i‖ ≤ 2*A*B := by
  rw [MaxwellRadiation.cross_component]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul,conjugate,Complex.norm_conj]
  have h1 := mul_le_mul (hu (WeakCurl.next i)) (hv (WeakCurl.previous i)) (norm_nonneg _) hA
  have h2 := mul_le_mul (hu (WeakCurl.previous i)) (hv (WeakCurl.next i)) (norm_nonneg _) hA
  linarith

theorem cross_perturbation_bound (E H E₀ H₀ : Vector) (A B D F : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hE : ∀ i, ‖E₀ i‖ ≤ A) (hH : ∀ i, ‖H i‖ ≤ B)
    (he : ∀ i, ‖E i-E₀ i‖ ≤ D) (hh : ∀ i, ‖H i-H₀ i‖ ≤ F)
    (hz : crossProduct E₀ (conjugate H₀) 2 = 0) :
    ‖crossProduct E (conjugate H) 2‖ ≤ 2*(D*B+A*F) := by
  have heq : crossProduct E (conjugate H) 2 =
      crossProduct (fun i => E i-E₀ i) (conjugate H) 2+
        crossProduct E₀ (conjugate (fun i => H i-H₀ i)) 2 := by
    simp [cross_apply,conjugate] at hz ⊢
    linear_combination hz
  rw [heq]
  apply (norm_add_le _ _).trans
  have h1 := cross_norm_bound _ H D B hD hB he hH 2
  have h2 := cross_norm_bound E₀ _ A F hA hF hE hh 2
  linarith

theorem leading_normal_cross_zero (k : ℝ) (ρ σ : Fin 3 → Space → ℂ)
    (x : Space) (hx : x ≠ 0) (hp : x 2 = 0) :
    crossProduct (leadingElectric k ρ x) (conjugate (leadingMagnetic k σ x)) 2 = 0 := by
  rw [show crossProduct (leadingElectric k ρ x) (conjugate (leadingMagnetic k σ x)) 2 =
    leadingElectric k ρ x 0*conj (leadingMagnetic k σ x 1)-
      leadingElectric k ρ x 1*conj (leadingMagnetic k σ x 0) from rfl]
  rw [← leading_radiation_identity k ρ x hx 0,← leading_radiation_identity k ρ x hx 1]
  simp [cross_apply,leadingMagnetic,direction,unitCoordinate,hp]
  ring

theorem potential_component_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (i : Fin 3) :
    ‖potential k ρ x i‖ ≤ sourceMass ρ/(2*Real.pi*‖x‖) := by
  have hs (y : Space) (hy : ρ i y ≠ 0) : y ∈ closedBall 0 R := by
    by_contra hn
    exact hy (hc i y hn)
  have h := response_norm_bound (phi k) (ρ i) (KernelIntegrability.phi_measurable k)
    (hρ i) x ((4*Real.pi)⁻¹*(2/‖x‖)) (fun y hy => phi_source_bound k R hR x y hx (hs y hy))
  apply h.trans
  calc
    _ ≤ ((4*Real.pi)⁻¹*(2/‖x‖))*sourceMass ρ :=
      mul_le_mul_of_nonneg_left (component_mass_le ρ i) (by positivity)
    _ = _ := by ring

def leadingConstant (k : ℝ) : ℝ := 3*k^2/Real.pi
def electricErrorConstant (k R : ℝ) : ℝ := 4*(k^2*R + |k| + 1)/Real.pi
def magneticErrorConstant (k R : ℝ) : ℝ := 2 * |k| * (2 * |k| * R+1)/Real.pi
def tailConstant (k R : ℝ) : ℝ :=
  2*(electricErrorConstant k R*(leadingConstant k+magneticErrorConstant k R)+
    leadingConstant k*magneticErrorConstant k R)

theorem leading_electric_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (i : Fin 3) :
    ‖leadingElectric k ρ x i‖ ≤ leadingConstant k*sourceMass ρ/‖x‖ := by
  have ht (j : Fin 3) :
      ‖(k : ℂ)^2*DyadicRadiation.transverse x i j*potential k ρ x j‖ ≤
        k^2*2*(sourceMass ρ/(2*Real.pi*‖x‖)) := by
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (DyadicRadiation.transverse_norm_bound x i j) (sq_nonneg k))
      (potential_component_bound k R hR ρ hρ hc x hx j) (norm_nonneg _) (by positivity)
  apply (norm_sum_le _ _).trans
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ht j)
  exact h.trans_eq (by simp only [Fin.sum_univ_three]; dsimp [leadingConstant]; ring)

theorem leading_magnetic_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (i : Fin 3) :
    ‖leadingMagnetic k ρ x i‖ ≤ leadingConstant k*sourceMass ρ/‖x‖ := by
  have hmass := sourceMass_nonnegative ρ
  have hb := cross_direction_bound (potential k ρ x) x (sourceMass ρ/(2*Real.pi*‖x‖))
    (by positivity) (potential_component_bound k R hR ρ hρ hc x hx) i
  have he : crossProduct (direction x) (potential k ρ x) i =
      -crossProduct (potential k ρ x) (direction x) i := by
    rw [cross_component,cross_component]
    ring
  simp only [leadingMagnetic,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,he,norm_neg]
  apply (mul_le_mul_of_nonneg_left hb (sq_nonneg k)).trans
  dsimp [leadingConstant]
  have hnorm : 0 < ‖x‖ := by linarith [norm_nonneg x]
  have hbase : 0 ≤ k^2*sourceMass ρ/(Real.pi*‖x‖) := by positivity
  convert (show k^2*sourceMass ρ/(Real.pi*‖x‖) ≤
      3*(k^2*sourceMass ρ/(Real.pi*‖x‖)) by linarith) using 1 <;> ring

theorem electric_error_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (i : Fin 3) :
    ‖ExteriorContinuity.electric k ρ x i-leadingElectric k ρ x i‖ ≤
      electricErrorConstant k R*sourceMass ρ/‖x‖^2 := by
  convert electric_transverse_bound k R hR ρ hρ hc x hx hx₂ i using 1
  dsimp [electricErrorConstant,sourceMass]
  ring

theorem magnetic_error_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (i : Fin 3) :
    ‖MagneticResponse.magnetic k ρ x i-leadingMagnetic k ρ x i‖ ≤
      magneticErrorConstant k R*sourceMass ρ/‖x‖^2 := by
  convert magnetic_transverse_bound k R hR ρ hρ hc x hx i using 1
  dsimp [magneticErrorConstant]
  ring

theorem magnetic_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (i : Fin 3) :
    ‖MagneticResponse.magnetic k ρ x i‖ ≤
      (leadingConstant k+magneticErrorConstant k R)*sourceMass ρ/‖x‖ := by
  have hmass := sourceMass_nonnegative ρ
  have hC : 0 ≤ magneticErrorConstant k R := by dsimp [magneticErrorConstant]; positivity
  have hp : 0 < ‖x‖ := by linarith
  have he := magnetic_error_bound k R hR ρ hρ hc x hx i
  have hl := leading_magnetic_bound k R hR ρ hρ hc x hx i
  have hn := norm_add_le (MagneticResponse.magnetic k ρ x i-leadingMagnetic k ρ x i)
    (leadingMagnetic k ρ x i)
  rw [sub_add_cancel] at hn
  have hd : magneticErrorConstant k R*sourceMass ρ/‖x‖^2 ≤
      magneticErrorConstant k R*sourceMass ρ/‖x‖ :=
    div_le_div_of_nonneg_left (mul_nonneg hC hmass) hp (by nlinarith)
  calc
    _ ≤ magneticErrorConstant k R*sourceMass ρ/‖x‖+
        leadingConstant k*sourceMass ρ/‖x‖ := hn.trans (add_le_add (he.trans hd) hl)
    _ = _ := by ring

def bilinearFlux (k : ℝ) (ρ σ : Fin 3 → Space → ℂ) (x : Space) : ℂ :=
  crossProduct (ExteriorContinuity.electric k ρ x)
    (conjugate (MagneticResponse.magnetic k σ x)) 2

theorem bilinear_flux_tail (k R : ℝ) (hR : 0 ≤ R)
    (ρ σ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hσ : ∀ j, Integrable (σ j))
    (hcρ : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (hcσ : ∀ j y, y ∉ closedBall 0 R → σ j y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hp : x 2 = 0) :
    ‖bilinearFlux k ρ σ x‖ ≤ tailConstant k R*sourceMass ρ*sourceMass σ/‖x‖^3 := by
  have hmassρ := sourceMass_nonnegative ρ
  have hmassσ := sourceMass_nonnegative σ
  have hL : 0 ≤ leadingConstant k := by dsimp [leadingConstant]; positivity
  have hE : 0 ≤ electricErrorConstant k R := by dsimp [electricErrorConstant]; positivity
  have hH : 0 ≤ magneticErrorConstant k R := by dsimp [magneticErrorConstant]; positivity
  have hnorm : 0 < ‖x‖ := by linarith
  have h := cross_perturbation_bound
    (ExteriorContinuity.electric k ρ x) (MagneticResponse.magnetic k σ x)
    (leadingElectric k ρ x) (leadingMagnetic k σ x)
    (leadingConstant k*sourceMass ρ/‖x‖)
    ((leadingConstant k+magneticErrorConstant k R)*sourceMass σ/‖x‖)
    (electricErrorConstant k R*sourceMass ρ/‖x‖^2)
    (magneticErrorConstant k R*sourceMass σ/‖x‖^2)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (leading_electric_bound k R hR ρ hρ hcρ x hx)
    (magnetic_bound k R hR σ hσ hcσ x hx hx₂)
    (electric_error_bound k R hR ρ hρ hcρ x hx hx₂)
    (magnetic_error_bound k R hR σ hσ hcσ x hx)
    (leading_normal_cross_zero k ρ σ x (norm_pos_iff.mp hnorm) hp)
  apply h.trans_eq
  dsimp [tailConstant]
  field_simp
  ring

theorem normal_power_tail (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hp : x 2 = 0) :
    |normalPower (ExteriorContinuity.electric k ρ x) (MagneticResponse.magnetic k ρ x)| ≤
      tailConstant k R*(sourceMass ρ)^2/(2*‖x‖^3) := by
  have h := bilinear_flux_tail k R hR ρ ρ hρ hρ hc hc x hx hx₂ hp
  have hr := Complex.abs_re_le_norm (bilinearFlux k ρ ρ x)
  change |(bilinearFlux k ρ ρ x).re/2| ≤ _
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (div_le_div_of_nonneg_right (hr.trans h) (by norm_num)).trans_eq (by ring)

def planePoint (q : PlaneInverseCube.Plane) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![q 0,q 1,0]

theorem planePoint_norm (q : PlaneInverseCube.Plane) : ‖planePoint q‖ = ‖q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_three,Fin.sum_univ_two]
  simp [planePoint]

theorem planePoint_continuous : Continuous planePoint := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact (EuclideanSpace.proj 0).continuous
  · exact (EuclideanSpace.proj 1).continuous
  · exact continuous_const

theorem bilinearFlux_continuousAt (k R : ℝ)
    (ρ σ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hσ : ∀ j, Integrable (σ j))
    (hcρ : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (hcσ : ∀ j y, y ∉ closedBall 0 R → σ j y = 0)
    (x : Space) (hx : R < ‖x‖) : ContinuousAt (bilinearFlux k ρ σ) x := by
  have he := ExteriorContinuity.electric_continuousAt k ρ hρ R hcρ x hx
  have hh := ExteriorContinuity.magnetic_continuousAt k σ hσ R hcσ x hx
  change ContinuousAt (fun y => ExteriorContinuity.electric k ρ y 0*conj (MagneticResponse.magnetic k σ y 1)-
    ExteriorContinuity.electric k ρ y 1*conj (MagneticResponse.magnetic k σ y 0)) x
  exact ((continuousAt_pi.mp he 0).mul (continuousAt_pi.mp hh 1).star).sub
    ((continuousAt_pi.mp he 1).mul (continuousAt_pi.mp hh 0).star)

theorem bilinear_plane_integrable (k R : ℝ) (hR : 0 ≤ R)
    (ρ σ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hσ : ∀ j, Integrable (σ j))
    (hcρ : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (hcσ : ∀ j y, y ∉ closedBall 0 R → σ j y = 0)
    (T : ℝ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) :
    IntegrableOn (fun q : PlaneInverseCube.Plane => bilinearFlux k ρ σ (planePoint q))
      {q : PlaneInverseCube.Plane | T < ‖q‖} := by
  have hb (q : PlaneInverseCube.Plane) (hq : T < ‖q‖) :
      ‖bilinearFlux k ρ σ (planePoint q)‖ ≤
        (tailConstant k R*sourceMass ρ*sourceMass σ)/‖q‖^3 := by
    simpa only [planePoint_norm] using bilinear_flux_tail k R hR ρ σ hρ hσ hcρ hcσ
      (planePoint q) (by rw [planePoint_norm]; linarith)
      (by rw [planePoint_norm]; linarith) (by rfl)
  have hcont : ContinuousOn (fun q : PlaneInverseCube.Plane => bilinearFlux k ρ σ (planePoint q))
      {q : PlaneInverseCube.Plane | T < ‖q‖} := by
    intro q hq
    exact ((bilinearFlux_continuousAt k R ρ σ hρ hσ hcρ hcσ (planePoint q)
      (by rw [planePoint_norm]; change T < ‖q‖ at hq; linarith)).comp
        planePoint_continuous.continuousAt).continuousWithinAt
  exact PlaneInverseCube.tail_integrable T _ (by linarith)
    (hcont.aestronglyMeasurable (isOpen_lt continuous_const continuous_norm).measurableSet) hb

theorem bilinear_plane_tail_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ σ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j)) (hσ : ∀ j, Integrable (σ j))
    (hcρ : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (hcσ : ∀ j y, y ∉ closedBall 0 R → σ j y = 0)
    (T : ℝ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) :
    (∫ q : PlaneInverseCube.Plane in {q : PlaneInverseCube.Plane | T < ‖q‖},
      ‖bilinearFlux k ρ σ (planePoint q)‖) ≤
        tailConstant k R*sourceMass ρ*sourceMass σ*PlaneInverseCube.diskConstant/T := by
  have hi := bilinear_plane_integrable k R hR ρ σ hρ hσ hcρ hcσ T hT hTR
  apply PlaneInverseCube.tail_integral_bound T _ (by linarith) hi.aestronglyMeasurable
  intro q hq
  simpa only [planePoint_norm] using bilinear_flux_tail k R hR ρ σ hρ hσ hcρ hcσ
    (planePoint q) (by rw [planePoint_norm]; linarith)
    (by rw [planePoint_norm]; linarith) (by rfl)

theorem normal_plane_integrable (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (T : ℝ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) :
    IntegrableOn (fun q : PlaneInverseCube.Plane =>
      normalPower (ExteriorContinuity.electric k ρ (planePoint q))
        (MagneticResponse.magnetic k ρ (planePoint q))) {q : PlaneInverseCube.Plane | T < ‖q‖} := by
  exact (bilinear_plane_integrable k R hR ρ ρ hρ hρ hc hc T hT hTR).re.div_const 2

theorem normal_plane_tail_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (T : ℝ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) :
    (∫ q : PlaneInverseCube.Plane in {q : PlaneInverseCube.Plane | T < ‖q‖},
      |normalPower (ExteriorContinuity.electric k ρ (planePoint q))
        (MagneticResponse.magnetic k ρ (planePoint q))|) ≤
      tailConstant k R*(sourceMass ρ)^2*PlaneInverseCube.diskConstant/(2*T) := by
  have hi := bilinear_plane_integrable k R hR ρ ρ hρ hρ hc hc T hT hTR
  have hn := normal_plane_integrable k R hR ρ hρ hc T hT hTR
  have hm : (∫ q : PlaneInverseCube.Plane in {q : PlaneInverseCube.Plane | T < ‖q‖},
      |normalPower (ExteriorContinuity.electric k ρ (planePoint q))
        (MagneticResponse.magnetic k ρ (planePoint q))|) ≤
      ∫ q : PlaneInverseCube.Plane in {q : PlaneInverseCube.Plane | T < ‖q‖},
        ‖bilinearFlux k ρ ρ (planePoint q)‖/2 := by
    apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using hn.norm) (hi.norm.div_const 2)
    filter_upwards with q
    change |(bilinearFlux k ρ ρ (planePoint q)).re/2| ≤ _
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by norm_num)
  rw [integral_div] at hm
  exact hm.trans ((div_le_div_of_nonneg_right
    (bilinear_plane_tail_bound k R hR ρ ρ hρ hρ hc hc T hT hTR) (by norm_num)).trans_eq (by ring))

end OQ14.MaxwellPlaneTail

#print axioms OQ14.MaxwellPlaneTail.cross_norm_bound
#print axioms OQ14.MaxwellPlaneTail.cross_perturbation_bound
#print axioms OQ14.MaxwellPlaneTail.leading_normal_cross_zero
#print axioms OQ14.MaxwellPlaneTail.potential_component_bound
#print axioms OQ14.MaxwellPlaneTail.leading_electric_bound
#print axioms OQ14.MaxwellPlaneTail.leading_magnetic_bound
#print axioms OQ14.MaxwellPlaneTail.electric_error_bound
#print axioms OQ14.MaxwellPlaneTail.magnetic_error_bound
#print axioms OQ14.MaxwellPlaneTail.magnetic_bound
#print axioms OQ14.MaxwellPlaneTail.bilinear_flux_tail
#print axioms OQ14.MaxwellPlaneTail.normal_power_tail
#print axioms OQ14.MaxwellPlaneTail.planePoint_norm
#print axioms OQ14.MaxwellPlaneTail.planePoint_continuous
#print axioms OQ14.MaxwellPlaneTail.bilinearFlux_continuousAt
#print axioms OQ14.MaxwellPlaneTail.bilinear_plane_integrable
#print axioms OQ14.MaxwellPlaneTail.bilinear_plane_tail_bound
#print axioms OQ14.MaxwellPlaneTail.normal_plane_integrable
#print axioms OQ14.MaxwellPlaneTail.normal_plane_tail_bound
