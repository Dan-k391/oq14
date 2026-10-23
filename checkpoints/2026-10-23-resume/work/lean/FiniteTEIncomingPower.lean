import SphereTangentialPower
import AngularFinitePairing

/-! The actual sphere flux limit identifies physical incoming power of finite TE waves. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteTEIncomingPower
open Complex Filter MeasureTheory Maxwell HarmonicPolynomial DebyeRadialTrace
open scoped Topology
variable {κ : Type*}

def angular (p : Poly) (j : Fin 3) : C(SphereReactionKernel.Sphere,ℂ) :=
  ⟨fun n => angularToroidal p n j,(continuous_apply j).comp
    ((HarmonicRadiationGeometry.angularToroidal_continuous p).comp continuous_subtype_val)⟩

def electric (s : Finset κ) (l : κ → ℕ) (p : κ → Poly) (A : κ → ℂ) : Field :=
  fun x j => ∑ i ∈ s, A i*RegularTEIncoming.electric (l i) true (p i) x j
def magnetic (s : Finset κ) (l : κ → ℕ) (p : κ → Poly) (A : κ → ℂ) : Field :=
  fun x j => ∑ i ∈ s, A i*RegularTEIncoming.magnetic (l i) true (p i) x j
def electricCoefficient (l : κ → ℕ) (A : κ → ℂ) (r : ℝ) (i : κ) : ℂ :=
  A i*(RegularTEIncoming.phase true r*RegularTEIncoming.radial (l i) true r)/2
def magneticCoefficient (l : κ → ℕ) (A : κ → ℂ) (r : ℝ) (i : κ) : ℂ :=
  A i*(I*(RegularTEIncoming.phase true r*RegularTEIncoming.radialD (l i) true r))/2
def amplitudeCoefficient (l : κ → ℕ) (A : κ → ℂ) (i : κ) : ℂ :=
  A i*RegularTEIncoming.coefficient (l i) true/2
def amplitude (s : Finset κ) (l : κ → ℕ) (p : κ → Poly) (A : κ → ℂ)
    (n : SphereReactionKernel.Sphere) : Vector :=
  fun j => ∑ i ∈ s, amplitudeCoefficient l A i*angular (p i) j n

theorem electric_coefficient_limit (l : κ → ℕ) (A : κ → ℂ) :
    Tendsto (electricCoefficient l A) atTop (𝓝 (amplitudeCoefficient l A)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact ((RegularTEIncoming.scaled_radial_limit (l i) true).const_mul (A i)).div_const 2

theorem magnetic_coefficient_limit (l : κ → ℕ) (A : κ → ℂ) :
    Tendsto (magneticCoefficient l A) atTop (𝓝 (amplitudeCoefficient l A)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h := (((RegularTEIncoming.scaled_radialD_limit (l i) true).const_mul I).const_mul (A i)).div_const 2
  convert h using 1
  dsimp [amplitudeCoefficient]
  ring_nf
  simp [I_sq]
  ring

theorem electric_ray (s : Finset κ) (l : κ → ℕ) (p : κ → Poly) (hp : ∀ i, (p i).IsHomogeneous (l i))
    (A : κ → ℂ) (n : SphereReactionKernel.Sphere) (r : ℝ) (hr : 0<r) :
    (RegularTEIncoming.phase true r*(r : ℂ)) • electric s l p A (r • (n : Space))=
      fun j => ∑ i ∈ s, electricCoefficient l A r i*angular (p i) j n := by
  ext j
  simp only [electric,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [RegularTEIncoming.electric_ray (l i) true (p i) (hp i) n r hr]
  dsimp [electricCoefficient,angular]
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  field_simp
  ring

theorem magnetic_tangent_ray (s : Finset κ) (l : κ → ℕ) (p : κ → Poly)
    (hp : ∀ i, (p i).IsHomogeneous (l i)) (hh : ∀ i, formalLaplacian (p i)=0)
    (A : κ → ℂ) (n : SphereReactionKernel.Sphere) (r : ℝ) (hr : 0<r) :
    (RegularTEIncoming.phase true r*(r : ℂ)) • crossProduct (position n) (magnetic s l p A (r • (n : Space)))=
      fun j => ∑ i ∈ s, magneticCoefficient l A r i*angular (p i) j n := by
  have hc : crossProduct (position n) (magnetic s l p A (r • (n : Space)))=
      ∑ i ∈ s, A i • crossProduct (position n) (RegularTEIncoming.magnetic (l i) true (p i) (r • (n : Space))) := by
    ext j
    fin_cases j <;> simp [magnetic,cross_apply,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib,Pi.smul_apply,mul_sub,mul_left_comm]
  rw [hc]
  ext j
  simp only [Finset.smul_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [RegularTEIncoming.magnetic_tangent_ray (l i) true (p i) (hp i) (hh i) n r hr]
  dsimp [magneticCoefficient,angular]
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  field_simp
  ring

def spherePower (s : Finset κ) (l : κ → ℕ) (p : κ → Poly) (A : κ → ℂ) (r : ℝ) : ℝ :=
  ∫ n : SphereReactionKernel.Sphere, -r^2*FarFieldPower.radialPower n
    (electric s l p A (r • (n : Space))) (magnetic s l p A (r • (n : Space))) ∂SphereReactionKernel.surface

def incomingPower (s : Finset κ) (l : κ → ℕ) (p : κ → Poly) (A : κ → ℂ) : ℝ :=
  (∫ n : SphereReactionKernel.Sphere, energy (amplitude s l p A n) ∂SphereReactionKernel.surface)/2

theorem sphere_power_pairing (s : Finset κ) (l : κ → ℕ) (p : κ → Poly)
    (hp : ∀ i, (p i).IsHomogeneous (l i)) (hh : ∀ i, formalLaplacian (p i)=0)
    (A : κ → ℂ) (r : ℝ) (hr : 0<r) :
    spherePower s l p A r=(AngularFinitePairing.pairing s (fun i => angular (p i))
      (electricCoefficient l A r) (magneticCoefficient l A r)).re/2 := by
  let u := electricCoefficient l A r
  let v := magneticCoefficient l A r
  have hc (w : κ → ℂ) (j : Fin 3) : Continuous (fun n : SphereReactionKernel.Sphere => ∑ i ∈ s, w i*angular (p i) j n) := by
    apply continuous_finset_sum
    intro i _
    exact continuous_const.mul (angular (p i) j).continuous
  have hcc (w : κ → ℂ) (j : Fin 3) := Complex.continuous_conj.comp (hc w j)
  have hi : Integrable (fun n : SphereReactionKernel.Sphere => dot (fun j => ∑ i ∈ s, u i*angular (p i) j n)
      (conjugate (fun j => ∑ i ∈ s, v i*angular (p i) j n))) SphereReactionKernel.surface := by
    exact ((((hc u 0).mul (hcc v 0)).add ((hc u 1).mul (hcc v 1))).add
      ((hc u 2).mul (hcc v 2))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [AngularFinitePairing.pairing_integral]
  calc
    _ = ∫ n : SphereReactionKernel.Sphere, (dot (fun j => ∑ i ∈ s, u i*angular (p i) j n)
        (conjugate (fun j => ∑ i ∈ s, v i*angular (p i) j n))).re/2 ∂SphereReactionKernel.surface := by
      apply integral_congr_ae
      filter_upwards with n
      have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
      rw [SphereTangentialPower.scaled_inward_power n hn,
        electric_ray s l p hp A n r hr,magnetic_tangent_ray s l p hp hh A n r hr]
    _ = _ := by rw [integral_div]; congr 1; exact integral_re hi

theorem actual_power_limit (s : Finset κ) (l : κ → ℕ) (p : κ → Poly)
    (hp : ∀ i, (p i).IsHomogeneous (l i)) (hh : ∀ i, formalLaplacian (p i)=0) (A : κ → ℂ) :
    Tendsto (spherePower s l p A) atTop (𝓝 (incomingPower s l p A)) := by
  have ht := ((AngularFinitePairing.pairing_continuous s (fun i => angular (p i))).tendsto
      (amplitudeCoefficient l A,amplitudeCoefficient l A)).comp
    ((electric_coefficient_limit l A).prodMk_nhds (magnetic_coefficient_limit l A))
  have ht' := ((Complex.continuous_re.tendsto _).comp ht).div_const 2
  rw [AngularFinitePairing.pairing_self] at ht'
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact (sphere_power_pairing s l p hp hh A r hr).symm

theorem incoming_power_nonnegative (s : Finset κ) (l : κ → ℕ) (p : κ → Poly) (A : κ → ℂ) :
    0 ≤ incomingPower s l p A :=
  div_nonneg (integral_nonneg (fun n => FarFieldPower.energy_nonnegative _)) (by norm_num)

theorem amplitude_energy_integrable (s : Finset κ) (l : κ → ℕ) (p : κ → Poly) (A : κ → ℂ) :
    Integrable (fun n : SphereReactionKernel.Sphere => energy (amplitude s l p A n)) SphereReactionKernel.surface :=
  AngularFinitePairing.energy_integrable s (fun i => angular (p i)) (amplitudeCoefficient l A)

end OQ14.FiniteTEIncomingPower
#print axioms OQ14.FiniteTEIncomingPower.electric_coefficient_limit
#print axioms OQ14.FiniteTEIncomingPower.magnetic_coefficient_limit
#print axioms OQ14.FiniteTEIncomingPower.electric_ray
#print axioms OQ14.FiniteTEIncomingPower.magnetic_tangent_ray
#print axioms OQ14.FiniteTEIncomingPower.sphere_power_pairing
#print axioms OQ14.FiniteTEIncomingPower.actual_power_limit
#print axioms OQ14.FiniteTEIncomingPower.incoming_power_nonnegative
#print axioms OQ14.FiniteTEIncomingPower.amplitude_energy_integrable
