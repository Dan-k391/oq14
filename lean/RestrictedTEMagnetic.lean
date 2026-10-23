import RestrictedTEAmplitude

/-! Actual magnetic Herglotz partner and global bounds for finite restricted TE inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEMagnetic
open Complex MeasureTheory Metric Set Maxwell DebyeRadialTrace
open RestrictedTEAmplitude RestrictedTEFields SymmetricHarmonicJets SphereWaveCalculus
open WeakCurl (next previous)
abbrev Space := FourierL2.Space
abbrev Sphere := SphereReactionKernel.Sphere

theorem density_bounded (A : Index →₀ ℂ) :
    ∃ B : ℝ, 0≤B ∧ ∀ n : Sphere, ∀ i : Fin 3, ‖density A n i‖≤B := by
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (univ : Set Sphere)).bddAbove_image
    (density_continuous A).norm.continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro n i
  exact (norm_le_pi_norm (density A n) i).trans
    ((hC (mem_image_of_mem _ (mem_univ n))).trans (le_max_right _ _))

def magneticDensity (A : Index →₀ ℂ) (n : Sphere) : Vector :=
  crossProduct (position n) (density A n)

theorem magnetic_density_continuous (A : Index →₀ ℂ) (i : Fin 3) :
    Continuous (fun n => magneticDensity A n i) := by
  have hc (j : Fin 3) : Continuous (fun n : Sphere => position n j) := coordinate_continuous j
  have hd (j : Fin 3) := (continuous_apply j).comp (density_continuous A)
  fin_cases i <;> exact ((hc _).mul (hd _)).sub ((hc _).mul (hd _))

theorem magnetic_herglotz (A : Index →₀ ℂ) (x : Space) (i : Fin 3) :
    DebyeMaxwell.teMagnetic 1 (potential 1 A) x i=
      ∫ n : Sphere, magneticDensity A n i*SphereReactionKernel.wave 1 x n ∂SphereReactionKernel.surface := by
  obtain ⟨B,hB,hb⟩ := density_bounded A
  have hc (j : Fin 3) : Continuous (fun n : Sphere => density A n j) :=
    (continuous_apply j).comp (density_continuous A)
  have he (j : Fin 3) : (fun y => DebyeMaxwell.teElectric (potential 1 A) y j)=
      moment (fun n => density A n j) 1 := funext (fun y => electric_herglotz A y j)
  have hp (a b : Fin 3) : dcoord (fun y => DebyeMaxwell.teElectric (potential 1 A) y b) x a=
      I*moment (fun n : Sphere => density A n b*(n.val a : ℂ)) 1 x := by
    rw [he,moment_partial _ (hc b) B (fun n => hb n b)]
    simp
  have hi (a b : Fin 3) : Integrable (fun n : Sphere =>
      (density A n b*(n.val a : ℂ))*SphereReactionKernel.wave 1 x n) SphereReactionKernel.surface :=
    moment_integrable _ ((hc b).mul (coordinate_continuous a)) B (fun n => by
      rw [norm_mul]
      exact (mul_le_mul (hb n b) (coordinate_bound a n) (norm_nonneg _) hB).trans_eq (by ring)) 1 x
  have hcurl : curl (DebyeMaxwell.teElectric (potential 1 A)) x i=
      dcoord (fun y => DebyeMaxwell.teElectric (potential 1 A) y (previous i)) x (next i)-
      dcoord (fun y => DebyeMaxwell.teElectric (potential 1 A) y (next i)) x (previous i) := by
    fin_cases i <;> rfl
  change (-I/1)*curl (DebyeMaxwell.teElectric (potential 1 A)) x i=_
  rw [hcurl,hp,hp]
  have hm : moment (fun n : Sphere => density A n (previous i)*(n.val (next i) : ℂ)) 1 x-
      moment (fun n : Sphere => density A n (next i)*(n.val (previous i) : ℂ)) 1 x=
      ∫ n : Sphere, magneticDensity A n i*SphereReactionKernel.wave 1 x n ∂SphereReactionKernel.surface := by
    unfold moment
    rw [← integral_sub (hi _ _) (hi _ _)]
    apply integral_congr_ae
    filter_upwards with n
    fin_cases i <;> simp [magneticDensity,position,cross_apply,next,previous] <;> ring
  calc
    _ = moment (fun n : Sphere => density A n (previous i)*(n.val (next i) : ℂ)) 1 x-
        moment (fun n : Sphere => density A n (next i)*(n.val (previous i) : ℂ)) 1 x := by
      simp only [div_one]; ring_nf; simp [I_sq,sub_eq_add_neg]
    _ = _ := hm

theorem magnetic_continuous (A : Index →₀ ℂ) (i : Fin 3) :
    Continuous (fun x => DebyeMaxwell.teMagnetic 1 (potential 1 A) x i) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact continuousAt_const.mul (ExteriorClassical.curl_smooth _
    (DebyeCalculus.toroidal_smooth _ x (potential_smooth 1 A).contDiffAt) i).continuousAt

theorem magnetic_bounded (A : Index →₀ ℂ) :
    ∃ B : ℝ, 0≤B ∧ ∀ x : Space, ∀ i : Fin 3,
      ‖DebyeMaxwell.teMagnetic 1 (potential 1 A) x i‖≤B := by
  have hc : Continuous (magneticDensity A) := continuous_pi (magnetic_density_continuous A)
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (univ : Set Sphere)).bddAbove_image hc.norm.continuousOn
  let D := max 0 C
  have hd (n : Sphere) (i : Fin 3) : ‖magneticDensity A n i‖≤D :=
    (norm_le_pi_norm _ i).trans ((hC (mem_image_of_mem _ (mem_univ n))).trans (le_max_right _ _))
  refine ⟨SphereReactionKernel.surfaceMass*D,?_ ,?_⟩
  · exact mul_nonneg (measureReal_nonneg) (le_max_left _ _)
  · intro x i
    rw [magnetic_herglotz]
    rw [mul_comm]
    change ‖∫ n : Sphere, magneticDensity A n i*SphereReactionKernel.wave 1 x n ∂SphereReactionKernel.surface‖≤
      D*SphereReactionKernel.surface.real univ
    apply norm_integral_le_of_norm_le_const
    filter_upwards with n
    simpa only [norm_mul,SphereReactionKernel.wave_norm,mul_one] using hd n i

end OQ14.RestrictedTEMagnetic
#print axioms OQ14.RestrictedTEMagnetic.density_bounded
#print axioms OQ14.RestrictedTEMagnetic.magnetic_density_continuous
#print axioms OQ14.RestrictedTEMagnetic.magnetic_herglotz
#print axioms OQ14.RestrictedTEMagnetic.magnetic_continuous
#print axioms OQ14.RestrictedTEMagnetic.magnetic_bounded
