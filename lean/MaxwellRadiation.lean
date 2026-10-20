import DyadicRadiation

/-! # Actual compact-source Maxwell radiation

The ordinary exterior electric integral and constructed magnetic response
are compared with a common transverse leading field.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.MaxwellRadiation

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel OQ14.KernelConvolution
  OQ14.ScalarRadiation OQ14.DyadicRadiation
open Filter
open scoped Topology

def direction (x : Space) : Vector := fun j => unitCoordinate j x

def potential (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) : Vector :=
  fun j => response (phi k) (ρ j) x

def leadingElectric (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) : Vector :=
  fun i => ∑ j : Fin 3, (k : ℂ)^2 * transverse x i j * potential k ρ x j

def leadingMagnetic (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) : Vector :=
  fun i => (k : ℂ)^2 * crossProduct (direction x) (potential k ρ x) i

def sourceMass (ρ : Fin 3 → Space → ℂ) : ℝ := ∑ j : Fin 3, ∫ y, ‖ρ j y‖

theorem sourceMass_nonnegative (ρ : Fin 3 → Space → ℂ) : 0 ≤ sourceMass ρ :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => norm_nonneg _))

theorem component_mass_le (ρ : Fin 3 → Space → ℂ) (j : Fin 3) :
    (∫ y, ‖ρ j y‖) ≤ sourceMass ρ := by
  unfold sourceMass
  exact Finset.single_le_sum
    (f := fun a : Fin 3 => ∫ y, ‖ρ a y‖)
    (fun _ _ => integral_nonneg (fun _ => norm_nonneg _)) (Finset.mem_univ j)

def gradientDefect (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) (i j : Fin 3) : ℂ :=
  response (fun z => phiGradient k z i) (ρ j) x -
    Complex.I * (k : ℂ) * unitCoordinate i x * potential k ρ x j

theorem direction_dot (x : Space) (hx : x ≠ 0) :
    dot (direction x) (direction x) = 1 := by
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hs := coordinate_squares x
  unfold dot direction unitCoordinate
  push_cast
  field_simp
  linear_combination hs

theorem cross_cross_same (u v : Vector) (i : Fin 3) :
    crossProduct (crossProduct u v) u i = dot u u * v i - dot u v * u i := by
  fin_cases i <;> simp [cross_apply, dot] <;> ring

theorem cross_const_left (a : ℂ) (u v : Vector) (i : Fin 3) :
    crossProduct (fun j => a * u j) v i = a * crossProduct u v i := by
  fin_cases i <;> simp [cross_apply] <;> ring

theorem leadingElectric_formula (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) (i : Fin 3) :
    leadingElectric k ρ x i =
      (k : ℂ)^2 * (potential k ρ x i - dot (direction x) (potential k ρ x) * direction x i) := by
  fin_cases i <;> simp [leadingElectric, Fin.sum_univ_three, transverse, direction, dot] <;> ring

theorem leading_radiation_identity (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    crossProduct (leadingMagnetic k ρ x) (direction x) i = leadingElectric k ρ x i := by
  unfold leadingMagnetic
  rw [cross_const_left, cross_cross_same, direction_dot x hx,
    one_mul, leadingElectric_formula]

theorem electric_transverse_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2 * R < ‖x‖) (hx2 : 2 ≤ ‖x‖) (i : Fin 3) :
    ‖ExteriorContinuity.electric k ρ x i - leadingElectric k ρ x i‖ ≤
      (4 * (k^2 * R + |k| + 1) / (Real.pi * ‖x‖^2)) *
        (∑ j : Fin 3, ∫ y, ‖ρ j y‖) := by
  simp only [ExteriorContinuity.electric, leadingElectric, potential, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => response_transverse_error k R hR (ρ j) (hρ j) (hc j)
    x hx hx2 i j)

theorem magnetic_defect_formula (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) (i : Fin 3) :
    MagneticResponse.magnetic k ρ x i - leadingMagnetic k ρ x i =
      -(Complex.I * (k : ℂ)) *
        (gradientDefect k ρ x (WeakCurl.next i) (WeakCurl.previous i) -
          gradientDefect k ρ x (WeakCurl.previous i) (WeakCurl.next i)) := by
  fin_cases i <;>
    simp [MagneticResponse.magnetic, leadingMagnetic, direction, gradientDefect, potential,
      WeakCurl.next, WeakCurl.previous, cross_apply] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem magnetic_transverse_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2 * R < ‖x‖) (i : Fin 3) :
    ‖MagneticResponse.magnetic k ρ x i - leadingMagnetic k ρ x i‖ ≤
      (2 * |k| * (2 * |k| * R + 1) / (Real.pi * ‖x‖^2)) * sourceMass ρ := by
  have hd (a b : Fin 3) : ‖gradientDefect k ρ x a b‖ ≤
      ((2 * |k| * R + 1) / (Real.pi * ‖x‖^2)) * sourceMass ρ :=
    (response_outgoing_bound k R hR (ρ b) (hρ b) (hc b) x hx a).trans
      (mul_le_mul_of_nonneg_left (component_mass_le ρ b) (by positivity))
  rw [magnetic_defect_formula, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |k| * (‖gradientDefect k ρ x (WeakCurl.next i) (WeakCurl.previous i)‖ +
      ‖gradientDefect k ρ x (WeakCurl.previous i) (WeakCurl.next i)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
    _ ≤ |k| * (2 * (((2 * |k| * R + 1) / (Real.pi * ‖x‖^2)) * sourceMass ρ)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      linarith [hd (WeakCurl.next i) (WeakCurl.previous i),
        hd (WeakCurl.previous i) (WeakCurl.next i)]
    _ = _ := by ring

theorem cross_component (u v : Vector) (i : Fin 3) :
    crossProduct u v i =
      u (WeakCurl.next i) * v (WeakCurl.previous i) -
        u (WeakCurl.previous i) * v (WeakCurl.next i) := by
  fin_cases i <;> simp [cross_apply, WeakCurl.next, WeakCurl.previous]

theorem cross_direction_bound (v : Vector) (x : Space) (B : ℝ) (hB : 0 ≤ B)
    (hv : ∀ j, ‖v j‖ ≤ B) (i : Fin 3) :
    ‖crossProduct v (direction x) i‖ ≤ 2 * B := by
  rw [cross_component]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul, direction]
  have h1 := mul_le_mul (hv (WeakCurl.next i))
    (unitCoordinate_norm_le (WeakCurl.previous i) x) (norm_nonneg _) hB
  have h2 := mul_le_mul (hv (WeakCurl.previous i))
    (unitCoordinate_norm_le (WeakCurl.next i) x) (norm_nonneg _) hB
  nlinarith

def radiationDefect (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) : Vector :=
  fun i => crossProduct (MagneticResponse.magnetic k ρ x) (direction x) i -
    ExteriorContinuity.electric k ρ x i

def radiationConstant (k R : ℝ) : ℝ :=
  4 * (|k| * (2 * |k| * R + 1) + k^2 * R + |k| + 1) / Real.pi

/-- The actual exterior fields obey a uniform inverse-square
Silver–Müller defect estimate. -/
theorem silver_mueller_bound (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (x : Space) (hx : 2 * R < ‖x‖) (hx2 : 2 ≤ ‖x‖) (i : Fin 3) :
    ‖radiationDefect k ρ x i‖ ≤ radiationConstant k R * sourceMass ρ / ‖x‖^2 := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : radiationDefect k ρ x i =
      crossProduct (fun j => MagneticResponse.magnetic k ρ x j - leadingMagnetic k ρ x j)
        (direction x) i -
      (ExteriorContinuity.electric k ρ x i - leadingElectric k ρ x i) := by
    rw [← leading_radiation_identity k ρ x hx0 i]
    simp only [radiationDefect, cross_component]
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  have hm := cross_direction_bound
    (fun j => MagneticResponse.magnetic k ρ x j - leadingMagnetic k ρ x j) x
    ((2 * |k| * (2 * |k| * R + 1) / (Real.pi * ‖x‖^2)) * sourceMass ρ)
    (mul_nonneg (by positivity) (sourceMass_nonnegative ρ))
    (magnetic_transverse_bound k R hR ρ hρ hc x hx) i
  have hE := electric_transverse_bound k R hR ρ hρ hc x hx hx2 i
  have hh := add_le_add hm hE
  convert hh using 1
  dsimp [radiationConstant, sourceMass]
  ring

/-- The uniform estimate gives radiation along every map whose norm tends
to infinity, over any index filter. -/
theorem silver_mueller_limit {α : Type*} {l : Filter α}
    (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (γ : α → Space) (hγ : Tendsto (fun t => ‖γ t‖) l atTop) (i : Fin 3) :
    Tendsto (fun t => (‖γ t‖ : ℂ) * radiationDefect k ρ (γ t) i) l (𝓝 0) := by
  let C := radiationConstant k R * sourceMass ρ
  have hl : Tendsto (fun t => C * (‖γ t‖)⁻¹) l (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hγ) :
        Tendsto (fun t => C * (‖γ t‖)⁻¹) l (𝓝 (C * 0)))
  apply squeeze_zero_norm' _ hl
  filter_upwards [hγ.eventually (eventually_gt_atTop (2*R)),
    hγ.eventually (eventually_gt_atTop 2)] with t ht ht2
  have hp : 0 < ‖γ t‖ := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  calc
    _ ≤ ‖γ t‖ * (radiationConstant k R * sourceMass ρ / ‖γ t‖^2) :=
      mul_le_mul_of_nonneg_left (silver_mueller_bound k R hR ρ hρ hc (γ t) ht ht2.le i)
        (norm_nonneg _)
    _ = C * (‖γ t‖)⁻¹ := by dsimp [C]; field_simp; ring

end OQ14.MaxwellRadiation

#print axioms OQ14.MaxwellRadiation.direction_dot
#print axioms OQ14.MaxwellRadiation.cross_cross_same
#print axioms OQ14.MaxwellRadiation.cross_const_left
#print axioms OQ14.MaxwellRadiation.leadingElectric_formula
#print axioms OQ14.MaxwellRadiation.leading_radiation_identity
#print axioms OQ14.MaxwellRadiation.electric_transverse_bound
#print axioms OQ14.MaxwellRadiation.sourceMass_nonnegative
#print axioms OQ14.MaxwellRadiation.component_mass_le
#print axioms OQ14.MaxwellRadiation.magnetic_defect_formula
#print axioms OQ14.MaxwellRadiation.magnetic_transverse_bound
#print axioms OQ14.MaxwellRadiation.cross_component
#print axioms OQ14.MaxwellRadiation.cross_direction_bound
#print axioms OQ14.MaxwellRadiation.silver_mueller_bound
#print axioms OQ14.MaxwellRadiation.silver_mueller_limit
