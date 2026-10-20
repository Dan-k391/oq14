import DynamicSupportVolume

/-! # Actual spherical-integral electric and magnetic wall reaction kernels

These are the explicit Herglotz kernels, with the genuine unit-sphere Haar
surface measure. Their uniform entry bounds are derived from this integral.
No equality with a finite radial background Green kernel is postulated.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.SphereReactionKernel

open MeasureTheory Metric
open scoped BigOperators InnerProductSpace

abbrev Space := FourierL2.Space
abbrev Sphere := sphere (0 : Space) 1

def surface : Measure Sphere := (volume : Measure Space).toSphere

instance : IsFiniteMeasure surface := inferInstanceAs
  (IsFiniteMeasure (volume : Measure Space).toSphere)

def surfaceMass : ℝ := surface.real Set.univ

def amplitude (θ : Sphere) (i j : Fin 3) : ℂ :=
  (if i = j then 1 else 0) - (θ.val i : ℂ) * (θ.val j : ℂ)

def wave (k : ℝ) (x : Space) (θ : Sphere) : ℂ :=
  Complex.exp (((k * ⟪θ.val, x⟫_ℝ : ℝ) : ℂ) * Complex.I)

def J (k : ℝ) (x : Space) (i j : Fin 3) : ℂ :=
  ((k^3 / (16*Real.pi^2) : ℝ) : ℂ) *
    ∫ θ : Sphere, amplitude θ i j * wave k x θ ∂surface

def entryBound (k : ℝ) : ℝ :=
  |k^3 / (16*Real.pi^2)| * (2 * surfaceMass)

theorem entryBound_nonnegative (k : ℝ) : 0 ≤ entryBound k := by
  unfold entryBound surfaceMass
  positivity

theorem sphere_norm (θ : Sphere) : ‖θ.val‖ = 1 := by
  simpa only [mem_sphere, dist_zero_right] using θ.property

theorem amplitude_bound (θ : Sphere) (i j : Fin 3) : ‖amplitude θ i j‖ ≤ 2 := by
  have hi : ‖(θ.val i : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, sphere_norm] using PiLp.norm_apply_le θ.val i
  have hj : ‖(θ.val j : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, sphere_norm] using PiLp.norm_apply_le θ.val j
  have hd : ‖(if i = j then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  exact (norm_sub_le _ _).trans (by rw [norm_mul]; nlinarith [norm_nonneg (θ.val i : ℂ), norm_nonneg (θ.val j : ℂ)])

theorem wave_norm (k : ℝ) (x : Space) (θ : Sphere) : ‖wave k x θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem integrand_bound (k : ℝ) (x : Space) (θ : Sphere) (i j : Fin 3) :
    ‖amplitude θ i j * wave k x θ‖ ≤ 2 := by
  rw [norm_mul, wave_norm, mul_one]
  exact amplitude_bound θ i j

theorem integrand_continuous (k : ℝ) (i j : Fin 3) :
    Continuous (fun p : Space × Sphere => amplitude p.2 i j * wave k p.1 p.2) := by
  have hθ : Continuous (fun p : Space × Sphere => p.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hi := Complex.continuous_ofReal.comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp hθ)
  have hj := Complex.continuous_ofReal.comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).continuous.comp hθ)
  exact (continuous_const.sub (hi.mul hj)).mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (hθ.inner continuous_fst))).mul continuous_const))

theorem integrand_integrable (k : ℝ) (x : Space) (i j : Fin 3) :
    Integrable (fun θ => amplitude θ i j * wave k x θ) surface := by
  apply (integrable_const (2 : ℝ)).mono'
    ((integrand_continuous k i j).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun θ => integrand_bound k x θ i j)

theorem J_bound (k : ℝ) (x : Space) (i j : Fin 3) : ‖J k x i j‖ ≤ entryBound k := by
  rw [J, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
      (fun θ => integrand_bound k x θ i j))) (abs_nonneg _)

theorem J_continuous (k : ℝ) (i j : Fin 3) : Continuous (fun x => J k x i j) := by
  apply continuous_const.mul
  apply continuous_of_dominated
    (fun x => (integrand_integrable k x i j).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun θ => integrand_bound k x θ i j))
    (integrable_const (2 : ℝ))
  filter_upwards with θ
  exact (integrand_continuous k i j).comp (continuous_id.prodMk continuous_const)

def sign (i : Fin 3) : ℝ := if i = 2 then -1 else 1

def reflect (x : Space) : Space := (WithLp.equiv 2 (Fin 3 → ℝ)).symm
  (fun i => sign i * x i)

theorem reflect_continuous : Continuous reflect := by
  apply (PiLp.continuous_equiv_symm 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  exact continuous_const.mul (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous

/-- electric=true subtracts the reflected electric term; false adds it. -/
def reaction (electric : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) : ℂ :=
  (Complex.I / 2) * (J k (x-y) i j +
    (if electric then -1 else 1 : ℂ) * (sign i : ℂ) * J k (reflect x-y) i j)

theorem reaction_continuous (electric : Bool) (k : ℝ) (i j : Fin 3) :
    Continuous (fun p : Space × Space => reaction electric k p.1 p.2 i j) := by
  unfold reaction
  exact continuous_const.mul (((J_continuous k i j).comp
    (continuous_fst.sub continuous_snd)).add (continuous_const.mul
      ((J_continuous k i j).comp ((reflect_continuous.comp continuous_fst).sub continuous_snd))))

theorem reaction_bound (electric : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    ‖reaction electric k x y i j‖ ≤ entryBound k := by
  have hs : ‖(sign i : ℂ)‖ = 1 := by unfold sign; split_ifs <;> norm_num
  have he : ‖(if electric then -1 else 1 : ℂ)‖ = 1 := by cases electric <;> norm_num
  unfold reaction
  rw [norm_mul]
  have hh := norm_add_le (J k (x-y) i j)
    ((if electric then -1 else 1 : ℂ) * (sign i : ℂ) * J k (reflect x-y) i j)
  simp only [norm_mul, hs, he, one_mul] at hh
  have hc : ‖Complex.I / 2‖ = 1/2 := by norm_num [norm_div]
  rw [hc]
  nlinarith [J_bound k (x-y) i j, J_bound k (reflect x-y) i j]

end OQ14.SphereReactionKernel

#print axioms OQ14.SphereReactionKernel.entryBound_nonnegative
#print axioms OQ14.SphereReactionKernel.sphere_norm
#print axioms OQ14.SphereReactionKernel.amplitude_bound
#print axioms OQ14.SphereReactionKernel.wave_norm
#print axioms OQ14.SphereReactionKernel.integrand_bound
#print axioms OQ14.SphereReactionKernel.integrand_continuous
#print axioms OQ14.SphereReactionKernel.integrand_integrable
#print axioms OQ14.SphereReactionKernel.J_bound
#print axioms OQ14.SphereReactionKernel.J_continuous
#print axioms OQ14.SphereReactionKernel.reflect_continuous
#print axioms OQ14.SphereReactionKernel.reaction_continuous
#print axioms OQ14.SphereReactionKernel.reaction_bound
