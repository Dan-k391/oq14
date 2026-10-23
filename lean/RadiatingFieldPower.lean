import RadialFlux
import ComponentAngularEnergy

/-! Physical flux and energy for actual fields with bounded outgoing far-field limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.RadiatingFieldPower
open MeasureTheory Metric Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.FarFieldPower OQ14.MaxwellFarField OQ14.AngularEnergy
open scoped Topology

theorem transverse_amplitude_power (n : Space) (hn : ‖n‖=1) (A : Vector)
    (hA : dot (MaxwellRadiation.direction n) A=0) :
    radialPower n A (crossProduct (MaxwellRadiation.direction n) A)=energy A/2 := by
  have hn0 : n≠0 := by intro h; simp [h] at hn
  unfold radialPower
  rw [transverse_power_identity _ _ (direction_conjugate n),
    MaxwellRadiation.direction_dot n hn0,hA,dot_conjugate,
    one_mul,zero_mul,sub_zero,Complex.ofReal_re]

theorem flux_limit (k : ℝ) (E H : Field) (A : Sphere → Vector)
    (htrans : ∀ n : Sphere, dot (MaxwellRadiation.direction n) (A n)=0)
    (hc : ∀ᶠ r : ℝ in atTop, Continuous (fun n : Sphere => E (r • (n : Space))) ∧
      Continuous (fun n : Sphere => H (r • (n : Space))))
    (hb : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop, ∀ n : Sphere, ∀ i : Fin 3,
      ‖factor k r*E (r • (n : Space)) i‖≤C ∧ ‖factor k r*H (r • (n : Space)) i‖≤C)
    (he : ∀ n : Sphere, Tendsto (fun r => factor k r • E (r • (n : Space))) atTop (𝓝 (A n)))
    (hh : ∀ n : Sphere, Tendsto (fun r => factor k r • H (r • (n : Space))) atTop
      (𝓝 (crossProduct (MaxwellRadiation.direction n) (A n)))) :
    Tendsto (RadialFlux.flux E H) atTop (𝓝 (∫ n : Sphere, energy (A n)/2 ∂angularMeasure)) := by
  obtain ⟨C,hC,hb⟩ := hb
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun _ : Sphere => 3*C^2)
  · filter_upwards [hc] with r hr
    exact (continuous_const.mul (radialPower_sphere_continuous _ _ hr.1 hr.2)).aestronglyMeasurable
  · filter_upwards [hb,eventually_gt_atTop (0 : ℝ)] with r hr hr0
    filter_upwards with n
    have h := radialPower_bound n (factor k r • E (r • (n : Space)))
      (factor k r • H (r • (n : Space))) C hC (fun i => (hr n i).1) (fun i => (hr n i).2)
    rwa [radialPower_smul,Complex.normSq_eq_norm_sq,factor_norm k r hr0] at h
  · exact integrable_const _
  · filter_upwards with n
    have h := ((radialPower_continuous n).tendsto
      (A n,crossProduct (MaxwellRadiation.direction n) (A n))).comp ((he n).prodMk_nhds (hh n))
    rw [transverse_amplitude_power n (sphere_norm n) (A n) (htrans n)] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [Function.comp_def,radialPower_smul,Complex.normSq_eq_norm_sq,factor_norm k r hr]

theorem far_energy_zero (k : ℝ) (ε : Space → ℝ)
    (hε : Measurable ε) (M : ℝ) (hbε : ∀ x, ‖ε x‖≤M) (E H : Field) (A : Sphere → Vector)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H)
    (htrans : ∀ n : Sphere, dot (MaxwellRadiation.direction n) (A n)=0)
    (hc : ∀ᶠ r : ℝ in atTop, Continuous (fun n : Sphere => E (r • (n : Space))) ∧
      Continuous (fun n : Sphere => H (r • (n : Space))))
    (hb : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop, ∀ n : Sphere, ∀ i : Fin 3,
      ‖factor k r*E (r • (n : Space)) i‖≤C ∧ ‖factor k r*H (r • (n : Space)) i‖≤C)
    (he : ∀ n : Sphere, Tendsto (fun r => factor k r • E (r • (n : Space))) atTop (𝓝 (A n)))
    (hh : ∀ n : Sphere, Tendsto (fun r => factor k r • H (r • (n : Space))) atTop
      (𝓝 (crossProduct (MaxwellRadiation.direction n) (A n)))) :
    (∫ n : Sphere, energy (A n) ∂angularMeasure)=0 := by
  have h := RadialFlux.nonnegative_limit_eq_zero (RadialFlux.flux E H)
    (∫ n : Sphere, energy (A n)/2 ∂angularMeasure)
    (integral_nonneg (fun n => div_nonneg (energy_nonnegative _) (by norm_num)))
    (flux_limit k E H A htrans hc hb he hh)
    (RadialFlux.maxwell_weighted_flux k ε hε M hbε E H hE hH hMax)
  rw [integral_div] at h
  linarith

theorem electric_mass_zero (k : ℝ) (ε : Space → ℝ)
    (hε : Measurable ε) (M : ℝ) (hbε : ∀ x, ‖ε x‖≤M) (E H : Field) (A : Sphere → Vector)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H)
    (htrans : ∀ n : Sphere, dot (MaxwellRadiation.direction n) (A n)=0)
    (hc : ∀ᶠ r : ℝ in atTop, Continuous (fun n : Sphere => E (r • (n : Space))) ∧
      Continuous (fun n : Sphere => H (r • (n : Space))))
    (hb : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop, ∀ n : Sphere, ∀ i : Fin 3,
      ‖factor k r*E (r • (n : Space)) i‖≤C ∧ ‖factor k r*H (r • (n : Space)) i‖≤C)
    (he : ∀ n : Sphere, Tendsto (fun r => factor k r • E (r • (n : Space))) atTop (𝓝 (A n)))
    (hh : ∀ n : Sphere, Tendsto (fun r => factor k r • H (r • (n : Space))) atTop
      (𝓝 (crossProduct (MaxwellRadiation.direction n) (A n)))) (i : Fin 3) :
    Tendsto (RadialMoment.sphericalMass (fun x => E x i)) atTop (𝓝 0) := by
  have hz := far_energy_zero k ε hε M hbε E H A hE hH hMax htrans hc hb he hh
  have hce := hc.mono (fun _ h => h.1)
  have hbe : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop, ∀ n : Sphere, ∀ j : Fin 3,
      ‖factor k r*E (r • (n : Space)) j‖≤C := by
    obtain ⟨C,hC,hb⟩ := hb
    exact ⟨C,hC,hb.mono (fun r hr n j => (hr n j).1)⟩
  have hl := spherical_energy_limit k E A hce hbe he
  rw [hz] at hl
  exact ComponentAngularEnergy.component_mass_tendsto_zero E hce hl i

end OQ14.RadiatingFieldPower
#print axioms OQ14.RadiatingFieldPower.transverse_amplitude_power
#print axioms OQ14.RadiatingFieldPower.flux_limit
#print axioms OQ14.RadiatingFieldPower.far_energy_zero
#print axioms OQ14.RadiatingFieldPower.electric_mass_zero
