import RadiatingMaxwellUniqueness

/-! Actual outgoing far-field data, subtraction, and the compact-source realization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.RadiatingTrace
open MeasureTheory Metric Filter OQ14.Maxwell OQ14.AngularPower OQ14.MaxwellFarField
open scoped Topology

structure Trace (k : ℝ) (E H : Field) where
  far : Sphere → Vector
  transverse : ∀ n : Sphere, dot (MaxwellRadiation.direction n) (far n)=0
  sphericalContinuous : ∀ᶠ r : ℝ in atTop,
    Continuous (fun n : Sphere => E (r • (n : Space))) ∧
      Continuous (fun n : Sphere => H (r • (n : Space)))
  bounded : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop, ∀ n : Sphere, ∀ i : Fin 3,
    ‖factor k r*E (r • (n : Space)) i‖≤C ∧ ‖factor k r*H (r • (n : Space)) i‖≤C
  electricLimit : ∀ n : Sphere,
    Tendsto (fun r => factor k r • E (r • (n : Space))) atTop (𝓝 (far n))
  magneticLimit : ∀ n : Sphere,
    Tendsto (fun r => factor k r • H (r • (n : Space))) atTop
      (𝓝 (crossProduct (MaxwellRadiation.direction n) (far n)))

def Trace.sub {k : ℝ} {E H E' H' : Field} (t : Trace k E H) (s : Trace k E' H') :
    Trace k (E-E') (H-H') where
  far n := t.far n-s.far n
  transverse n := by
    have h : dot (MaxwellRadiation.direction n) (t.far n-s.far n)=
        dot (MaxwellRadiation.direction n) (t.far n)-dot (MaxwellRadiation.direction n) (s.far n) := by
      simp only [dot,Pi.sub_apply]
      ring
    rw [h,t.transverse n,s.transverse n,sub_self]
  sphericalContinuous := by
    filter_upwards [t.sphericalContinuous,s.sphericalContinuous] with r hr hs
    exact ⟨hr.1.sub hs.1,hr.2.sub hs.2⟩
  bounded := by
    obtain ⟨C,hC,hb⟩ := t.bounded
    obtain ⟨D,hD,hd⟩ := s.bounded
    refine ⟨C+D,add_nonneg hC hD,?_⟩
    filter_upwards [hb,hd] with r hr hs n i
    simp only [Pi.sub_apply,mul_sub]
    exact ⟨(norm_sub_le _ _).trans (add_le_add (hr n i).1 (hs n i).1),
      (norm_sub_le _ _).trans (add_le_add (hr n i).2 (hs n i).2)⟩
  electricLimit n := by
    simpa only [Pi.sub_apply,smul_sub] using (t.electricLimit n).sub (s.electricLimit n)
  magneticLimit n := by
    simpa only [Pi.sub_apply,smul_sub,map_sub] using (t.magneticLimit n).sub (s.magneticLimit n)

def compactSource (k R : ℝ) (hR : 0≤R) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y=0) :
    Trace k (ExteriorContinuity.representative k F ρ R) (MagneticResponse.magnetic k ρ) where
  far n := electricAmplitude k ρ n
  transverse n := amplitude_transverse k ρ n (sphere_norm n)
  sphericalContinuous := by
    filter_upwards [eventually_gt_atTop R] with r hr
    have he : (fun n : Sphere => ExteriorContinuity.representative k F ρ R (r • (n : Space)))=
        fun n : Sphere => ExteriorContinuity.electric k ρ (r • (n : Space)) := by
      funext n
      apply ExteriorContinuity.representative_exterior
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (hR.trans_lt hr),sphere_norm,mul_one] using hr
    rw [he]
    exact actual_fields_sphere_continuous k R r hR hr ρ hρ hs
  bounded := by
    obtain ⟨C,hC,hb⟩ := actual_fields_uniform_bound k R hR ρ hρ hs
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_gt_atTop (max (2*R) 2),eventually_gt_atTop R] with r hr hrR n i
    rw [ExteriorContinuity.representative_exterior k F ρ R _ (by
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (hR.trans_lt hrR),sphere_norm,mul_one] using hrR)]
    exact hb r hr n (sphere_norm n) i
  electricLimit n := by
    apply (electric_far_vector_limit k R hR ρ hρ hs n (sphere_norm n)).congr'
    filter_upwards [eventually_gt_atTop R] with r hr
    rw [ExteriorContinuity.representative_exterior k F ρ R _ (by
      simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos (hR.trans_lt hr),sphere_norm,mul_one] using hr)]
  magneticLimit n := by
    rw [amplitude_tangential_relation]
    exact magnetic_far_vector_limit k R hR ρ hρ hs n (sphere_norm n)

theorem representative_smooth (k R : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y=0) (i : Fin 3) (x : Space) (hx : R<‖x‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => ExteriorContinuity.representative k F ρ R z i) x := by
  apply ContDiffAt.congr_of_eventuallyEq
    (contDiffAt_pi.mp (ExteriorSmooth.electric_contDiffAt k ρ hρ R hs x hx) i)
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  rw [ExteriorContinuity.representative_exterior k F ρ R y hy]

theorem vacuum_zero (k : ℝ) (hk : 0<k) (R : ℝ) (hR : 0≤R) (E H : Field)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k (fun _ => 1) E H)
    (hEs : ∀ i x, R<‖x‖ → ContDiffAt ℝ (⊤ : ℕ∞) (fun z => E z i) x)
    (t : Trace k E H) : (E =ᵐ[volume] 0) ∧ (H =ᵐ[volume] 0) :=
  RadiatingMaxwellUniqueness.vacuum_fields_zero k hk R hR E H t.far hE hH hMax hEs
    t.transverse t.sphericalContinuous t.bounded t.electricLimit t.magneticLimit

end OQ14.RadiatingTrace
#print axioms OQ14.RadiatingTrace.Trace.sub
#print axioms OQ14.RadiatingTrace.compactSource
#print axioms OQ14.RadiatingTrace.representative_smooth
#print axioms OQ14.RadiatingTrace.vacuum_zero
