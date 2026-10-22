import LayerMagneticProfiles

/-! The actual second Maxwell equation through all interfaces of a finite TM chain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.LayerMagneticMaxwell
open MeasureTheory Set Filter OQ14.Maxwell OQ14.RadialStack OQ14.RadialGluing
  OQ14.ClippedLayerProfiles OQ14.LayerElectricProfiles OQ14.HarmonicPolynomial
open scoped Topology

theorem profile_layer_germ (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (s : State) (r : ℝ) (hr : R<r) (hrX : r≤X) (hcut : r∉cuts gs) :
    ∃ g∈gs,∃ α β : ℂ,
      (profile l gs s =ᶠ[𝓝 r] fun t =>
        (RadialLayer.value l g.q g.σ α β t,RadialLayer.momentum l g.q g.σ α β t)) ∧
      sigmaAt gs r=g.σ ∧ inverseSigma gs r=(g.σ : ℂ)⁻¹ := by
  induction h generalizing s with
  | nil R => exact (not_lt_of_ge hrX hr).elim
  | cons g gs R h ih =>
    by_cases hgr : g.a<r
    · refine ⟨g,List.mem_cons_self,RadialLayer.initialAlpha l g.q g.σ g.b s.1 s.2,
        RadialLayer.initialBeta l g.q g.σ g.b s.1 s.2,?_,?_,?_⟩
      · filter_upwards [Ioi_mem_nhds hgr] with t ht
        simp only [profile,if_pos (show g.a<t from ht),wave,waveMomentum]
      · simp only [sigmaAt,if_pos hgr]
      · simp only [inverseSigma,select,if_pos hgr]
    · have hn : r≠g.a := by intro he; apply hcut; simp [cuts,he]
      have hlt : r<g.a := lt_of_le_of_ne (not_lt.mp hgr) hn
      have ht : r∉cuts gs := fun hm => hcut (List.mem_cons_of_mem _ hm)
      obtain ⟨g',hmem,α,β,hg,hσ,hi⟩ := ih (back l g s) hr (not_lt.mp hgr) ht
      refine ⟨g',List.mem_cons_of_mem _ hmem,α,β,?_,?_,?_⟩
      · filter_upwards [Iio_mem_nhds hlt,hg] with t ht he
        simpa only [profile,if_neg (not_lt.mpr (show t≤g.a from le_of_lt ht))] using he
      · simpa only [sigmaAt,if_neg hgr] using hσ
      · simpa only [inverseSigma,select,if_neg hgr] using hi

theorem second_pointwise (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (k : ℝ) (hdisp : ∀ g∈gs,g.q^2=k^2*g.σ) (s : State)
    (c : ℝ) (hc : 0<c) (hcR : c≤R) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (x : Space)
    (hr : R<‖x‖) (hrX : ‖x‖≤X) (hcut : ‖x‖∉cuts gs) :
    curl (LayerElectricMaxwell.magnetic l gs s c k p) x=
      fun j => -(Complex.I*(k : ℂ)*(sigmaAt gs ‖x‖ : ℂ))*LayerElectricMaxwell.electric l gs s c p x j := by
  have hcx : c<‖x‖ := hcR.trans_lt hr
  have hx : x≠0 := norm_pos_iff.mp (hc.trans hcx)
  obtain ⟨g,hg,α,β,hprof,hσ,hinv⟩ := profile_layer_germ l h s ‖x‖ hr hrX hcut
  have hm : LayerElectricMaxwell.magnetic l gs s c k p =ᶠ[𝓝 x]
      RiccatiTransmission.tmH l (k : ℂ) (RadialLayer.value l g.q g.σ α β) p := by
    have hsp := continuous_norm.continuousAt.eventually hprof
    have hcl : ∀ᶠ y : Space in 𝓝 x,c<‖y‖ := continuous_norm.continuousAt.eventually (Ioi_mem_nhds hcx)
    filter_upwards [hsp,hcl] with y hy hyc
    have hy0 : y≠0 := norm_pos_iff.mp (hc.trans hyc)
    ext j
    simp only [LayerElectricMaxwell.magnetic,quotient,value,state,radius,max_eq_right hyc.le,hy,
      RiccatiTransmission.tmH,Pi.smul_apply,smul_eq_mul,RiccatiDebyeTrace.M]
    rw [DebyeRadialTrace.toroidal_components _
      (RadialLayerMaxwell.profile_smooth l g.q g.σ α β g.q_pos.ne') p y hy0]
    simp only [RadialQuotient.profile,mul_assoc]
  have he : LayerElectricMaxwell.electric l gs s c p x=
      RiccatiTransmission.tmE l (g.σ : ℂ) (RadialLayer.value l g.q g.σ α β) p x := by
    ext j
    rw [LayerElectricMaxwell.homogeneous_electric_components l g.q g.σ α β
      g.q_pos.ne' g.σ_pos.ne' p hp hh x hx]
    simp only [LayerElectricMaxwell.electric,RadialNormalPrimitive.electric,a,b,
      quotient,value,momentum,state,radius,max_eq_right hcx.le,hprof.eq_of_nhds,hinv]
    ring
  rw [ExteriorClassical.curl_congr_nhds hm]
  have hMax := (RadialLayerMaxwell.tm_maxwell l g.q g.σ k g.σ α β
    g.q_pos.ne' g.σ_pos.ne' g.σ_pos.ne' (hdisp g hg) p hp hh x hx).2
  rw [he,hσ]
  simpa only [Complex.ofReal_one,mul_one,neg_mul] using hMax

theorem second_weak_maxwell (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (k : ℝ) (hdisp : ∀ g∈gs,g.q^2=k^2*g.σ) (s : State)
    (c : ℝ) (hc : 0<c) (hcR : c≤R) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hcompact : HasCompactSupport φ)
    (hs : tsupport φ ⊆ {x : Space | R<‖x‖ ∧ ‖x‖<X}) :
    weakCurlPairing (LayerElectricMaxwell.magnetic l gs s c k p) φ=
      fun j => ∫ x, (-(Complex.I*(k : ℂ)*(sigmaAt gs ‖x‖ : ℂ))*
        LayerElectricMaxwell.electric l gs s c p x j)*φ x := by
  rw [LayerMagneticProfiles.magnetic_weak_curl l h s c k hc p φ hφ hcompact]
  have he : {r : ℝ | r∈cuts gs}=(cuts gs).toFinset := by ext r; simp
  have hS : {r : ℝ | r∈cuts gs}.Countable := he ▸ (cuts gs).toFinset.finite_toSet.countable
  ext j
  apply integral_congr_ae
  filter_upwards [SphericalInterfaces.ae_off_interfaces _ hS] with x hx
  by_cases ht : x∈tsupport φ
  · obtain ⟨hr,hX⟩ := hs ht
    rw [second_pointwise l h k hdisp s c hc hcR p hp hh x hr hX.le hx]
  · rw [image_eq_zero_of_nmem_tsupport ht,mul_zero,mul_zero]

end OQ14.LayerMagneticMaxwell

#print axioms OQ14.LayerMagneticMaxwell.profile_layer_germ
#print axioms OQ14.LayerMagneticMaxwell.second_pointwise
#print axioms OQ14.LayerMagneticMaxwell.second_weak_maxwell
