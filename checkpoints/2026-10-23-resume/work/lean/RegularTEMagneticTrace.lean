import RegularTEIncoming

/-! Actual radial magnetic trace of the incoming and outgoing TE components. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RegularTEMagneticTrace
open Complex Filter Maxwell HarmonicPolynomial DebyeRadialTrace RegularTEIncoming
open scoped Topology
abbrev Space := FourierL2.Space
abbrev Sphere := SphereReactionKernel.Sphere

theorem magnetic_radial_ray (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (n : Sphere) (r : ℝ) (hr : 0<r) :
    dot (position n) (magnetic l inward p (r • (n : Space)))=
      (-I*(l : ℂ)*(l+1)*radial l inward r/(2*(r : ℂ)^2))*complexEvaluate p n := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hnorm : ‖r • (n : Space)‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
  have hx : r • (n : Space)≠0 := norm_pos_iff.mp (by rw [hnorm]; exact hr)
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  have hp0 : position (r • (n : Space))=(r : ℂ) • position n := by
    ext i
    simp [position,PiLp.smul_apply]
  have hN := RiccatiDebyeTrace.N_radial l (radial l inward) (profile_smooth l inward) p hp hh
    (r • (n : Space)) hx
  rw [hp0,hnorm,FischerDecomposition.complexEvaluate_smul p l hp] at hN
  have hd : (r : ℂ)*dot (position n) (RiccatiDebyeTrace.N l (radial l inward) p (r • (n : Space)))=
      (l : ℂ)*(l+1)*radial l inward r/(r : ℂ)*complexEvaluate p n := by
    calc
      _ = dot ((r : ℂ) • position n) (RiccatiDebyeTrace.N l (radial l inward) p (r • (n : Space))) := by
        simp only [dot,Pi.smul_apply,smul_eq_mul]
        ring
      _ = _ := by
        rw [hN]
        field_simp [hrc,pow_succ]
        ring
  have hd' : dot (position n) (RiccatiDebyeTrace.N l (radial l inward) p (r • (n : Space)))=
      (l : ℂ)*(l+1)*radial l inward r/(r : ℂ)^2*complexEvaluate p n := by
    apply (mul_left_cancel₀ hrc)
    rw [hd]
    field_simp
    ring
  have hm : dot (position n) (magnetic l inward p (r • (n : Space)))=
      (-I/2)*dot (position n) (RiccatiDebyeTrace.N l (radial l inward) p (r • (n : Space))) := by
    simp only [magnetic,RiccatiTransmission.teH,div_one,dot,Pi.smul_apply,smul_eq_mul]
    ring
  rw [hm,hd']
  ring

theorem phase_norm (inward : Bool) (r : ℝ) : ‖phase inward r‖=1 := by
  cases inward <;> simp [phase,Complex.norm_exp]

theorem radial_eventually_bounded (l : ℕ) (inward : Bool) :
    ∀ᶠ r : ℝ in atTop, ‖radial l inward r‖≤2 := by
  have ht := (scaled_radial_limit l inward).norm
  have hc : ‖coefficient l inward‖=1 := by cases inward <;> simp [coefficient]
  simp only [norm_mul,phase_norm,one_mul,hc] at ht
  filter_upwards [(tendsto_order.1 ht).2 2 (by norm_num)] with r hr
  exact hr.le

theorem radialD_eventually_bounded (l : ℕ) (inward : Bool) :
    ∀ᶠ r : ℝ in atTop, ‖radialD l inward r‖≤2 := by
  have ht := (scaled_radialD_limit l inward).norm
  have hc : ‖coefficient l inward*(if inward then -I else I)‖=1 := by cases inward <;> simp [coefficient]
  simp only [norm_mul,phase_norm,one_mul] at ht
  rw [← norm_mul,hc] at ht
  filter_upwards [(tendsto_order.1 ht).2 2 (by norm_num)] with r hr
  exact hr.le

end OQ14.RegularTEMagneticTrace
#print axioms OQ14.RegularTEMagneticTrace.magnetic_radial_ray
#print axioms OQ14.RegularTEMagneticTrace.phase_norm
#print axioms OQ14.RegularTEMagneticTrace.radial_eventually_bounded
#print axioms OQ14.RegularTEMagneticTrace.radialD_eventually_bounded
