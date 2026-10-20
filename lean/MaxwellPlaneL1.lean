import PlaneSourceKernel

/-! # Whole-plane L1 bounds and continuity for actual separated Maxwell sources

Actual compact kernels control the bounded observation disk; actual transverse
radiation controls its complement. Constants depend only on frequency, the
common source ball and its positive gap from the plane.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.MaxwellPlaneL1

open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.MaxwellRadiation
  OQ14.MaxwellPlaneTail OQ14.PlaneSourceKernel
open scoped Topology

def flux (k : ℝ) (ρ σ : Source) (q : Plane) : ℂ := bilinearFlux k ρ σ (planePoint q)

def envelope (T A B : ℝ) (q : Plane) : ℝ :=
  (closedBall (0 : Plane) T).indicator (fun _ => A) q+B*PlaneInverseCube.profile T ‖q‖

theorem envelope_integrable (T A B : ℝ) (hT : 0 < T) : Integrable (envelope T A B) := by
  have hloc : Integrable ((closedBall (0 : Plane) T).indicator (fun _ => A)) :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (integrableOn_const.mpr (Or.inr (isCompact_closedBall (0 : Plane) T).measure_lt_top))
  exact hloc.add ((PlaneInverseCube.inverse_cube_integrable T hT).const_mul B)

theorem envelope_nonnegative (T A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (q : Plane) :
    0 ≤ envelope T A B q := by
  unfold envelope
  apply add_nonneg
  · exact Set.indicator_nonneg (fun _ _ => hA) q
  · apply mul_nonneg hB
    by_cases ht : T < ‖q‖
    · simp only [PlaneInverseCube.profile,Set.indicator,mem_Ioi,if_pos ht]
      positivity
    · simp [PlaneInverseCube.profile,Set.indicator,ht]

theorem global_envelope (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ w : Plane → ℝ, Integrable w ∧ (∀ q, 0 ≤ w q) ∧
      ∀ ρ σ : Source, Admissible R d ρ → Admissible R d σ →
        ∀ q : Plane, ‖flux k ρ σ q‖ ≤ w q*sourceMass ρ*sourceMass σ := by
  let T := max (2*R) 2+1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right (2*R) 2]
  have hT₂ : 2 ≤ T := by dsimp [T]; linarith [le_max_right (2*R) 2]
  have hTR : 2*R ≤ T := by dsimp [T]; linarith [le_max_left (2*R) 2]
  obtain ⟨C,hC,hlocal⟩ := local_field_bounds k R d T hd
  let A := 4 * |k| * C^2
  let B := tailConstant k R
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    dsimp [B,tailConstant,leadingConstant,electricErrorConstant,magneticErrorConstant]
    positivity
  refine ⟨envelope T A B,envelope_integrable T A B hT,envelope_nonnegative T A B hA hB,?_⟩
  intro ρ σ hρ hσ q
  have hmρ := sourceMass_nonnegative ρ
  have hmσ := sourceMass_nonnegative σ
  by_cases hq : ‖q‖ ≤ T
  · have hE := (hlocal ρ hρ q hq).1
    have hH := (hlocal σ hσ q hq).2
    have hb := cross_norm_bound _ _ (C*sourceMass ρ) (2 * |k| * C*sourceMass σ)
      (by positivity) (by positivity) hE hH 2
    have he : envelope T A B q = A := by
      simp [envelope,PlaneInverseCube.profile,Set.indicator,mem_closedBall,dist_zero_right,hq,not_lt.mpr hq]
    rw [he]
    exact hb.trans_eq (by dsimp [A]; ring)
  · have ht : T < ‖q‖ := lt_of_not_ge hq
    have hb := bilinear_flux_tail k R hR ρ σ hρ.integrable hσ.integrable hρ.support hσ.support
      (planePoint q) (by rw [planePoint_norm]; linarith) (by rw [planePoint_norm]; linarith) (by rfl)
    have he : envelope T A B q = B/‖q‖^3 := by
      simp [envelope,PlaneInverseCube.profile,Set.indicator,mem_closedBall,dist_zero_right,hq,ht,div_eq_mul_inv]
    rw [he]
    exact hb.trans_eq (by dsimp [B]; rw [planePoint_norm]; ring)

theorem whole_plane_bound (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ σ : Source, Admissible R d ρ → Admissible R d σ →
      Integrable (flux k ρ σ) ∧ (∫ q : Plane, ‖flux k ρ σ q‖) ≤ C*sourceMass ρ*sourceMass σ := by
  obtain ⟨w,hw,hpos,hbound⟩ := global_envelope k R d hR hd
  refine ⟨∫ q, w q,integral_nonneg hpos,?_⟩
  intro ρ σ hρ hσ
  have hi : Integrable (flux k ρ σ) :=
    ((hw.mul_const (sourceMass ρ)).mul_const (sourceMass σ)).mono'
      (bilinear_plane_continuous k R d hd ρ σ hρ hσ).aestronglyMeasurable
      (Eventually.of_forall (hbound ρ σ hρ hσ))
  refine ⟨hi,?_⟩
  have hm := integral_mono_ae hi.norm ((hw.mul_const (sourceMass ρ)).mul_const (sourceMass σ))
    (Eventually.of_forall (hbound ρ σ hρ hσ))
  simpa only [integral_mul_const] using hm

theorem whole_plane_difference_bound (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ σ ρ' σ' : Source,
      Admissible R d ρ → Admissible R d σ → Admissible R d ρ' → Admissible R d σ' →
      Integrable (fun q => flux k ρ σ q-flux k ρ' σ' q) ∧
        (∫ q : Plane, ‖flux k ρ σ q-flux k ρ' σ' q‖) ≤
          C*(sourceMass (ρ-ρ')*sourceMass σ+sourceMass ρ'*sourceMass (σ-σ')) := by
  obtain ⟨C,hC,hbound⟩ := whole_plane_bound k R d hR hd
  refine ⟨C,hC,?_⟩
  intro ρ σ ρ' σ' hρ hσ hρ' hσ'
  have hi := (hbound ρ σ hρ hσ).1.sub (hbound ρ' σ' hρ' hσ').1
  have h₁ := hbound (ρ-ρ') σ (admissible_sub R d ρ ρ' hρ hρ') hσ
  have h₂ := hbound ρ' (σ-σ') hρ' (admissible_sub R d σ σ' hσ hσ')
  refine ⟨hi,?_⟩
  have hm : (∫ q : Plane, ‖flux k ρ σ q-flux k ρ' σ' q‖) ≤
      (∫ q : Plane, ‖flux k (ρ-ρ') σ q‖)+(∫ q : Plane, ‖flux k ρ' (σ-σ') q‖) := by
    rw [← integral_add h₁.1.norm h₂.1.norm]
    apply integral_mono_ae hi.norm (h₁.1.norm.add h₂.1.norm)
    filter_upwards with q
    change ‖bilinearFlux k ρ σ (planePoint q)-bilinearFlux k ρ' σ' (planePoint q)‖ ≤ _
    rw [bilinear_plane_sub k R d hd ρ σ ρ' σ' hρ hσ hρ' hσ' q]
    exact norm_add_le _ _
  exact (hm.trans (add_le_add h₁.2 h₂.2)).trans_eq (by ring)

theorem source_convergence {α : Type*} {l : Filter α}
    (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (ρ σ : Source) (ρn σn : α → Source)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (hρn : ∀ a, Admissible R d (ρn a)) (hσn : ∀ a, Admissible R d (σn a))
    (hconvρ : Tendsto (fun a => sourceMass (ρn a-ρ)) l (𝓝 0))
    (hconvσ : Tendsto (fun a => sourceMass (σn a-σ)) l (𝓝 0)) :
    Tendsto (fun a => ∫ q : Plane, ‖flux k (ρn a) (σn a) q-flux k ρ σ q‖) l (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := whole_plane_difference_bound k R d hR hd
  have hb (a : α) : (∫ q : Plane, ‖flux k (ρn a) (σn a) q-flux k ρ σ q‖) ≤
      C*(sourceMass (ρn a-ρ)*(sourceMass (σn a-σ)+sourceMass σ)+
        sourceMass ρ*sourceMass (σn a-σ)) := by
    apply ((hbound (ρn a) (σn a) ρ σ (hρn a) (hσn a) hρ hσ).2).trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_left
      (sourceMass_le_sub_add (σn a) σ (hσn a).integrable hσ.integrable)
      (sourceMass_nonnegative _)
  have ht : Tendsto (fun a => C*(sourceMass (ρn a-ρ)*(sourceMass (σn a-σ)+sourceMass σ)+
      sourceMass ρ*sourceMass (σn a-σ))) l (𝓝 0) := by
    have h : Tendsto (fun a => C*(sourceMass (ρn a-ρ)*(sourceMass (σn a-σ)+sourceMass σ)+
        sourceMass ρ*sourceMass (σn a-σ))) l (𝓝 (C*(0*(0+sourceMass σ)+sourceMass ρ*0))) :=
      tendsto_const_nhds.mul ((hconvρ.mul (hconvσ.add tendsto_const_nhds)).add
        (tendsto_const_nhds.mul hconvσ))
    simpa only [zero_add,mul_zero,zero_mul,add_zero] using h
  exact squeeze_zero (fun a => integral_nonneg (fun _ => norm_nonneg _)) hb ht

def power (k : ℝ) (ρ : Source) (q : Plane) : ℝ :=
  normalPower (ExteriorContinuity.electric k ρ (planePoint q)) (MagneticResponse.magnetic k ρ (planePoint q))

theorem power_integrable (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d)
    (ρ : Source) (hρ : Admissible R d ρ) : Integrable (power k ρ) := by
  obtain ⟨_,_,hbound⟩ := whole_plane_bound k R d hR hd
  exact (hbound ρ ρ hρ hρ).1.re.div_const 2

theorem power_source_convergence {α : Type*} {l : Filter α}
    (k R d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (ρ : Source) (ρn : α → Source)
    (hρ : Admissible R d ρ) (hρn : ∀ a, Admissible R d (ρn a))
    (hconv : Tendsto (fun a => sourceMass (ρn a-ρ)) l (𝓝 0)) :
    Tendsto (fun a => ∫ q : Plane, |power k (ρn a) q-power k ρ q|) l (𝓝 0) := by
  have ht := source_convergence k R d hR hd ρ ρ ρn ρn hρ hρ hρn hρn hconv hconv
  have hb (a : α) : (∫ q : Plane, |power k (ρn a) q-power k ρ q|) ≤
      (∫ q : Plane, ‖flux k (ρn a) (ρn a) q-flux k ρ ρ q‖)/2 := by
    obtain ⟨_,_,hbound⟩ := whole_plane_difference_bound k R d hR hd
    have hi := (hbound (ρn a) (ρn a) ρ ρ (hρn a) (hρn a) hρ hρ).1
    have hn := (power_integrable k R d hR hd (ρn a) (hρn a)).sub
      (power_integrable k R d hR hd ρ hρ)
    rw [← integral_div]
    apply integral_mono_ae (by simpa only [Real.norm_eq_abs] using hn.norm) (hi.norm.div_const 2)
    filter_upwards with q
    have he : power k (ρn a) q-power k ρ q =
        (flux k (ρn a) (ρn a) q-flux k ρ ρ q).re/2 := by
      simp only [power,normalPower,flux,bilinearFlux,Complex.sub_re]
      ring
    rw [he,abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (by norm_num)
  have hz : Tendsto (fun a => (∫ q : Plane, ‖flux k (ρn a) (ρn a) q-flux k ρ ρ q‖)/2) l (𝓝 0) := by
    simpa only [zero_div] using ht.div_const 2
  exact squeeze_zero (fun a => integral_nonneg (fun _ => abs_nonneg _)) hb hz

end OQ14.MaxwellPlaneL1

#print axioms OQ14.MaxwellPlaneL1.envelope_integrable
#print axioms OQ14.MaxwellPlaneL1.envelope_nonnegative
#print axioms OQ14.MaxwellPlaneL1.global_envelope
#print axioms OQ14.MaxwellPlaneL1.whole_plane_bound
#print axioms OQ14.MaxwellPlaneL1.whole_plane_difference_bound
#print axioms OQ14.MaxwellPlaneL1.source_convergence
#print axioms OQ14.MaxwellPlaneL1.power_integrable
#print axioms OQ14.MaxwellPlaneL1.power_source_convergence
