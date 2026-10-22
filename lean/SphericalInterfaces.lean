import SphereRemovable

/-! Genuine weak derivatives across countably many spherical interfaces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.SphericalInterfaces
open MeasureTheory Metric OQ14.Maxwell OQ14.PointSingularity OQ14.SphereRemovable Filter Set
open scoped Topology

theorem coordinate_exception_countable (S : Set ℝ) (hS : S.Countable) (i : Fin 3) (q : Plane) :
    {t : ℝ | ‖(split i).symm (t,q)‖ ∈ S}.Countable := by
  have he : {t : ℝ | ‖(split i).symm (t,q)‖ ∈ S}=
      ⋃ r ∈ S, {t : ℝ | ‖(split i).symm (t,q)‖=r} := by
    ext t
    simp only [mem_setOf_eq,mem_iUnion,exists_prop]
    exact ⟨fun h => ⟨_,h,rfl⟩,fun ⟨r,hr,he⟩ => he.symm ▸ hr⟩
  rw [he]
  exact hS.biUnion (fun r _ => (coordinate_line_sphere_finite i q r).countable)

theorem ae_off_interfaces (S : Set ℝ) (hS : S.Countable) :
    ∀ᵐ x : Space, ‖x‖ ∉ S := by
  have he : {x : Space | ‖x‖ ∈ S}=⋃ r ∈ S, sphere (0 : Space) r := by
    ext x
    simp only [mem_setOf_eq,mem_iUnion,mem_sphere,dist_zero_right,exists_prop]
    exact ⟨fun h => ⟨_,h,rfl⟩,fun ⟨r,hr,he⟩ => he.symm ▸ hr⟩
  rw [ae_iff]
  simp only [not_not]
  rw [he]
  exact measure_biUnion_null_iff hS |>.mpr (fun r _ => Measure.addHaar_sphere volume (0 : Space) r)

theorem integration_by_parts (S : Set ℝ) (hS : S.Countable) (i : Fin 3) (f g : Space → ℂ)
    (hfc : Continuous f) (hgc : Continuous g) (hcompact : HasCompactSupport g)
    (hf : ∀ x, x≠0 → ‖x‖ ∉ S → DifferentiableAt ℝ f x)
    (hg : ∀ x, DifferentiableAt ℝ g x)
    (hleft : Integrable (fun x => dcoord f x i*g x))
    (hright : Integrable (fun x => f x*dcoord g x i)) :
    (∫ x, f x*dcoord g x i)=-(∫ x, dcoord f x i*g x) := by
  rw [coordinate_Fubini i _ hright,coordinate_Fubini i _ hleft,← integral_neg]
  apply integral_congr_ae
  filter_upwards [(split_integrable i _ hleft).prod_left_ae,
    (split_integrable i _ hright).prod_left_ae,
    show ∀ᵐ q : Plane, q≠0 from ae_iff.mpr (by simp)] with q hl hr hq
  have he := integral_derivative_off_countable
    (fun t => f ((split i).symm (t,q))*g ((split i).symm (t,q)))
    (fun t => dcoord f ((split i).symm (t,q)) i*g ((split i).symm (t,q))+
      f ((split i).symm (t,q))*dcoord g ((split i).symm (t,q)) i)
    {t | ‖(split i).symm (t,q)‖ ∈ S}
    (coordinate_exception_countable S hS i q)
    ((hfc.comp (line_continuous i q)).mul (hgc.comp (line_continuous i q)))
    (line_compact_support i q _ hcompact).mul_left
    (fun t ht => ((hf _ (join_ne_zero i q hq t) ht).hasFDerivAt.comp_hasDerivAt t
      (join_hasDerivAt i q t)).mul
      ((hg _).hasFDerivAt.comp_hasDerivAt t (join_hasDerivAt i q t)))
    (hl.add hr)
  rw [integral_add hl hr] at he
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)

theorem weak_partial (S : Set ℝ) (hS : S.Countable) (i : Fin 3) (f f' : Space → ℂ)
    (hc : Continuous f)
    (hf : ∀ x, x≠0 → ‖x‖ ∉ S → DifferentiableAt ℝ f x)
    (hder : ∀ x, x≠0 → ‖x‖ ∉ S → dcoord f x i=f' x)
    (hdloc : LocallyIntegrable f')
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    (∫ x, f' x*φ x)=-(∫ x, f x*dcoord φ x i) := by
  have he : (fun x => f' x*φ x)=ᵐ[volume] (fun x => dcoord f x i*φ x) := by
    filter_upwards [ae_off_interfaces S hS,
      show ∀ᵐ x : Space, x≠0 from ae_iff.mpr (by simp)] with x hx hx0
    rw [hder x hx0 hx]
  have hl := (test_product_integrable f' φ hdloc hφ.continuous hcompact).congr he
  have hr := test_product_integrable f (fun x => dcoord φ x i) hc.locallyIntegrable
    (partial_continuous hφ i) (hcompact.fderiv_apply ℝ (basis i))
  have hb := integration_by_parts S hS i f φ hc hφ.continuous hcompact hf
    (fun x => hφ.differentiable le_rfl x) hl hr
  rw [integral_congr_ae he]
  simpa only [neg_neg] using congrArg Neg.neg hb.symm

theorem curl_integration_by_parts (S : Set ℝ) (hS : S.Countable) (F : Field)
    (hc : ∀ j, Continuous (fun x => F x j))
    (hd : ∀ x, x≠0 → ‖x‖ ∉ S → ∀ j, DifferentiableAt ℝ (fun y => F y j) x)
    (hloc : ∀ i j, LocallyIntegrable (fun x => pd F x i j))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    (fun j => ∫ x, curl F x j*φ x)=weakCurlPairing F φ := by
  have hI (i j : Fin 3) := test_product_integrable _ φ (hloc i j) hφ.continuous hcompact
  have hP (i j : Fin 3) := weak_partial S hS i (fun x => F x j) (fun x => pd F x i j)
    (hc j) (fun x hx0 hx => hd x hx0 hx j) (fun _ _ _ => rfl) (hloc i j) φ hφ hcompact
  ext j
  fin_cases j <;> dsimp [curl,weakCurlPairing] <;> simp only [sub_mul]
  · rw [integral_sub (hI 1 2) (hI 2 1),hP 1 2,hP 2 1]
    ring
  · rw [integral_sub (hI 2 0) (hI 0 2),hP 2 0,hP 0 2]
    ring
  · rw [integral_sub (hI 0 1) (hI 1 0),hP 0 1,hP 1 0]
    ring

theorem gradient_curl_zero (S : Set ℝ) (hS : S.Countable) (f : Space → ℂ) (G : Field)
    (hc : Continuous f)
    (hf : ∀ x, x≠0 → ‖x‖ ∉ S → DifferentiableAt ℝ f x)
    (hder : ∀ x, x≠0 → ‖x‖ ∉ S → ∀ i, dcoord f x i=G x i)
    (hloc : ∀ i, LocallyIntegrable (fun x => G x i))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing G φ=0 := by
  have hp (j : Fin 3) : ContDiff ℝ 1 (fun x => dcoord φ x j) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ φ) := (contDiff_succ_iff_fderiv (n := 1)).mp hφ |>.2.2
    exact hd.clm_apply contDiff_const
  have hpair (i j : Fin 3) : (∫ x, G x i*dcoord φ x j)=∫ x, G x j*dcoord φ x i := by
    rw [weak_partial S hS i f (fun x => G x i) hc hf (fun x h0 hx => hder x h0 hx i)
        (hloc i) _ (hp j) (hcompact.fderiv_apply ℝ (basis j)),
      weak_partial S hS j f (fun x => G x j) hc hf (fun x h0 hx => hder x h0 hx j)
        (hloc j) _ (hp i) (hcompact.fderiv_apply ℝ (basis i))]
    congr 1
    apply integral_congr_ae
    filter_upwards with x
    rw [partial_comm hφ x i j]
  ext j
  fin_cases j <;> dsimp [weakCurlPairing] <;> rw [hpair] <;> simp

end OQ14.SphericalInterfaces

#print axioms OQ14.SphericalInterfaces.coordinate_exception_countable
#print axioms OQ14.SphericalInterfaces.ae_off_interfaces
#print axioms OQ14.SphericalInterfaces.integration_by_parts
#print axioms OQ14.SphericalInterfaces.weak_partial
#print axioms OQ14.SphericalInterfaces.curl_integration_by_parts
#print axioms OQ14.SphericalInterfaces.gradient_curl_zero
