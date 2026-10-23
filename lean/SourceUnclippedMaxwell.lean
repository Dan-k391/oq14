import SourceMagneticProfiles

/-! Actual punctured-space weak Maxwell equations, independent of the auxiliary source clipping. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.SourceUnclippedMaxwell
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem

def electric (d : Data) (p : HarmonicPolynomial.Poly) : Field := fun x i =>
  ((raw d ‖x‖).2/(‖x‖ : ℂ)^d.l)*dcoord (HarmonicPolynomial.complexEvaluate p) x i+
    (inverseSigma d ‖x‖*((d.l : ℂ)*(d.l+1)*(raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+3))-
      (d.l : ℂ)*(raw d ‖x‖).2/(‖x‖ : ℂ)^(d.l+2))*(x i : ℂ)*HarmonicPolynomial.complexEvaluate p x

def magnetic (d : Data) (p : HarmonicPolynomial.Poly) : Field := fun x i =>
  -Complex.I*((raw d ‖x‖).1/(‖x‖ : ℂ)^(d.l+1))*DebyeRadialTrace.angularToroidal p x i

def reclip (d : Data) (c : ℝ) (hc : 0<c) : Data := { d with c:=c, hc:=hc }

theorem electric_agrees (d : Data) (c : ℝ) (hc : 0<c) (p : HarmonicPolynomial.Poly)
    (x : Space) (hx : c<‖x‖) : SourceElectricProfiles.electric (reclip d c hc) p x=electric d p x := by
  ext i
  simp only [SourceElectricProfiles.electric,RadialNormalPrimitive.electric,SourceElectricProfiles.a,
    SourceElectricProfiles.b,SourceElectricProfiles.value,SourceElectricProfiles.momentum,
    LayerElectricProfiles.quotient,state,ClippedLayerProfiles.radius,reclip,max_eq_right hx.le,electric,raw]
  simp only [inverseSigma]
  ring

theorem magnetic_agrees (d : Data) (c : ℝ) (hc : 0<c) (p : HarmonicPolynomial.Poly)
    (x : Space) (hx : c<‖x‖) : SourceElectricProfiles.magnetic (reclip d c hc) p x=magnetic d p x := by
  ext i
  simp only [SourceElectricProfiles.magnetic,SourceElectricProfiles.value,LayerElectricProfiles.quotient,
    state,ClippedLayerProfiles.radius,reclip,max_eq_right hx.le,magnetic,raw]

theorem weakCurlPairing_congr_on_support (E F : Field) (φ : Space → ℂ)
    (he : ∀ x∈tsupport φ,E x=F x) : weakCurlPairing E φ=weakCurlPairing F φ := by
  have hi (j i : Fin 3) : (∫ x,E x j*dcoord φ x i)=∫ x,F x j*dcoord φ x i := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x∈tsupport φ
    · rw [he x hx]
    · simp only [dcoord,fderiv_of_not_mem_tsupport ℝ hx,ContinuousLinearMap.zero_apply,mul_zero]
  ext j
  fin_cases j <;> simp only [weakCurlPairing,hi]

theorem compact_test_gap (φ : Space → ℂ) (h0 : 0∉tsupport φ) :
    ∃ c : ℝ,0<c ∧ tsupport φ ⊆ {x : Space | c<‖x‖} := by
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp ((isClosed_tsupport φ).isOpen_compl.mem_nhds h0)
  refine ⟨ε/2,by linarith,?_⟩
  intro x hx
  have hn : ε≤‖x‖ := by
    by_contra h
    have hb : x∈ball (0 : Space) ε := by simpa only [mem_ball,dist_zero_right] using not_le.mp h
    exact hsub hb hx
  change ε/2<‖x‖
  linarith

theorem first_weak_maxwell (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (p : HarmonicPolynomial.Poly)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ)
    (h0 : 0∉tsupport φ) :
    weakCurlPairing (electric d p) φ=fun i => ∫ x,(Complex.I*magnetic d p x i)*φ x := by
  obtain ⟨c,hc,hs⟩ := compact_test_gap φ h0
  rw [← weakCurlPairing_congr_on_support (SourceElectricProfiles.electric (reclip d c hc) p)
    (electric d p) φ (fun x hx => electric_agrees d c hc p x (hs hx))]
  rw [SourceElectricProfiles.first_weak_maxwell (reclip d c hc) hdisp p φ hφ hcompact hs]
  ext i
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈tsupport φ
  · rw [magnetic_agrees d c hc p x (hs hx)]
  · rw [image_eq_zero_of_nmem_tsupport hx,mul_zero,mul_zero]

theorem second_weak_maxwell (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0)
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ)
    (h0 : 0∉tsupport φ) :
    weakCurlPairing (magnetic d p) φ=fun i => ∫ x,(-Complex.I*sigma d ‖x‖*electric d p x i)*φ x := by
  obtain ⟨c,hc,hs⟩ := compact_test_gap φ h0
  rw [← weakCurlPairing_congr_on_support (SourceElectricProfiles.magnetic (reclip d c hc) p)
    (magnetic d p) φ (fun x hx => magnetic_agrees d c hc p x (hs hx))]
  rw [SourceMagneticProfiles.second_weak_maxwell (reclip d c hc) p hp hh φ hφ hcompact hs]
  ext i
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x∈tsupport φ
  · rw [electric_agrees d c hc p x (hs hx)]
    rfl
  · rw [image_eq_zero_of_nmem_tsupport hx,mul_zero,mul_zero]

end OQ14.SourceUnclippedMaxwell

#print axioms OQ14.SourceUnclippedMaxwell.electric_agrees
#print axioms OQ14.SourceUnclippedMaxwell.magnetic_agrees
#print axioms OQ14.SourceUnclippedMaxwell.weakCurlPairing_congr_on_support
#print axioms OQ14.SourceUnclippedMaxwell.compact_test_gap
#print axioms OQ14.SourceUnclippedMaxwell.first_weak_maxwell
#print axioms OQ14.SourceUnclippedMaxwell.second_weak_maxwell
