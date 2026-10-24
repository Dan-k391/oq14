import SourceFarAmplitude

/-! Single-mode exterior plane flux: for one layered source mode, the normal flux density on the
plane z = 0 outside the stack is bounded by a constant times the inverse cube of the distance. The
leading tangential cross product has no normal component on the plane; only the radial electric
component survives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceRemotePlaneFlux
open Complex Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.SourceRadiation OQ14.ModalAlgebra OQ14.SourceFarAmplitude
open scoped Topology ComplexConjugate

theorem toroidal_dot (P : Poly) (x : Space) :
    (x 0 : ℂ)*DebyeRadialTrace.angularToroidal P x 0+(x 1 : ℂ)*DebyeRadialTrace.angularToroidal P x 1+
      (x 2 : ℂ)*DebyeRadialTrace.angularToroidal P x 2=0 := by
  simp only [DebyeRadialTrace.angularToroidal]
  simp
  ring

theorem cross_zero (a b : Vector) : crossProduct a b 0=a 1*b 2-a 2*b 1 := rfl
theorem cross_one (a b : Vector) : crossProduct a b 1=a 2*b 0-a 0*b 2 := rfl
theorem cross_two (a b : Vector) : crossProduct a b 2=a 0*b 1-a 1*b 0 := rfl

theorem poloidal_cross_zero (P : Poly) (x : Space) (hx : x 2=0) :
    crossProduct (HarmonicRadiationFactors.poloidal P x)
      (conjugate (DebyeRadialTrace.angularToroidal P x)) 2=0 := by
  have h := toroidal_dot P x
  rw [hx] at h
  simp only [Complex.ofReal_zero,zero_mul,add_zero] at h
  have hc := congrArg (starRingEnd ℂ) h
  simp only [map_add,map_mul,Complex.conj_ofReal,map_zero] at hc
  simp only [HarmonicRadiationFactors.poloidal,DebyeRadialTrace.position,cross_two,cross_zero,cross_one,
    conjugate,hx,Complex.ofReal_zero]
  linear_combination (DebyeRadialTrace.angularToroidal P x 2)*hc

theorem cross_smul (c c' : ℂ) (a b : Vector) :
    crossProduct (c • a) (conjugate (c' • b)) 2=c*(starRingEnd ℂ) c'*crossProduct a (conjugate b) 2 := by
  simp only [cross_two,conjugate,Pi.smul_apply,smul_eq_mul,map_mul]
  ring

theorem cross_add_smul (A B : ℂ) (a a' : Vector) (c : ℂ) (t : Vector) :
    crossProduct (A • a+B • a') (conjugate (c • t)) 2=
      A*(starRingEnd ℂ) c*crossProduct a (conjugate t) 2+B*(starRingEnd ℂ) c*crossProduct a' (conjugate t) 2 := by
  simp only [cross_two,conjugate,Pi.smul_apply,Pi.add_apply,smul_eq_mul,map_mul]
  ring

theorem cross_component_bound (a t : Vector) (A T : ℝ) (ha : ‖a‖ ≤ A) (ht : ‖t‖ ≤ T) :
    ‖crossProduct a (conjugate t) 2‖ ≤ 2*A*T := by
  have hA : 0 ≤ A := (norm_nonneg _).trans ha
  have hT : 0 ≤ T := (norm_nonneg _).trans ht
  have hc (i : Fin 3) : ‖conjugate t i‖ ≤ T := by
    have : ‖conjugate t i‖=‖t i‖ := by simp [conjugate]
    rw [this]
    exact (norm_le_pi_norm t i).trans ht
  have hai (i : Fin 3) : ‖a i‖ ≤ A := (norm_le_pi_norm a i).trans ha
  rw [cross_two]
  calc _ ≤ ‖a 0*conjugate t 1‖+‖a 1*conjugate t 0‖ := norm_sub_le _ _
    _ ≤ A*T+A*T := by
      rw [norm_mul,norm_mul]
      exact add_le_add (mul_le_mul (hai 0) (hc 1) (norm_nonneg _) hA)
        (mul_le_mul (hai 1) (hc 0) (norm_nonneg _) hA)
    _ = _ := by ring

theorem plane_flux_bound (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ∃ r0 C : ℝ, 0 ≤ C ∧ ∀ x : Space, x 2=0 → r0 ≤ ‖x‖ → d.X<‖x‖ →
      ‖crossProduct (SourceUnclippedMaxwell.electric d P x)
        (conjugate (SourceUnclippedMaxwell.magnetic d P x)) 2‖ ≤ C/‖x‖^3 := by
  obtain ⟨M1,hM1,h1⟩ := HarmonicRadiationFactors.radial_bound P d.l hp
  obtain ⟨M2,hM2,h2⟩ := HarmonicRadiationGeometry.normalized_toroidal_bound P d.l hp
  have hpol : Tendsto (fun r : ℝ => p d.l r) atTop (𝓝 1) := by
    simpa only [one_mul] using RadialRellich.hankelPoly_radial_limit d.l 1 (by norm_num) I
  obtain ⟨r1,hr1⟩ := eventually_atTop.mp (hpol.norm.eventually (gt_mem_nhds (by norm_num : ‖(1 : ℂ)‖<2)))
  refine ⟨max r1 1,8*‖amplitude d‖^2*((d.l : ℝ)*(d.l+1))*M1*M2,by positivity,?_⟩
  intro x hx2 hr hX
  have hr1' : r1 ≤ ‖x‖ := (le_max_left _ _).trans hr
  have hrpos : 0<‖x‖ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hr)
  have hx0 : x≠0 := norm_pos_iff.mp hrpos
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hpb : ‖p d.l ‖x‖‖ ≤ 2 := (hr1 _ hr1').le
  have hun : Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹*(Complex.exp (-I*(‖x‖ : ℂ))*(‖x‖ : ℂ))=1 := by
    have he : Complex.exp (I*(‖x‖ : ℂ))*Complex.exp (-I*(‖x‖ : ℂ))=1 := by
      rw [← Complex.exp_add]; simp
    calc _ = (Complex.exp (I*(‖x‖ : ℂ))*Complex.exp (-I*(‖x‖ : ℂ)))*((‖x‖ : ℂ)⁻¹*(‖x‖ : ℂ)) := by ring
      _ = 1 := by rw [he,inv_mul_cancel₀ hr0,one_mul]
  have hE : SourceUnclippedMaxwell.electric d P x=
      (Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹) • electricWeighted d P x := by
    unfold electricWeighted
    rw [smul_smul,hun,one_smul]
  have hH : SourceUnclippedMaxwell.magnetic d P x=
      (Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹) • magneticWeighted d P x := by
    unfold magneticWeighted
    rw [smul_smul,hun,one_smul]
  have hcn : ‖Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹‖=‖x‖⁻¹ := by
    have he : ‖Complex.exp (I*(‖x‖ : ℂ))‖=1 := by
      rw [Complex.norm_exp]; simp
    rw [norm_mul,he,one_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrpos]
  have hcj (z : ℂ) : ‖(starRingEnd ℂ) z‖=‖z‖ := by simp
  have hphase : ‖phase d.l‖=1 := by
    simp [SourceRadiation.phase]
  rw [hE,hH,electric_exterior d P hp x hX,magnetic_exterior d P x hX,cross_smul,
    cross_add_smul _ _ (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.poloidal P x)
      (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.radial P x)]
  have hz : crossProduct (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.poloidal P x)
      (conjugate (((‖x‖ : ℂ)^d.l)⁻¹ • DebyeRadialTrace.angularToroidal P x)) 2=0 := by
    rw [cross_smul,poloidal_cross_zero P x hx2]
    ring
  rw [hz,mul_zero,zero_add]
  have hX1 : ‖crossProduct (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.radial P x)
      (conjugate (((‖x‖ : ℂ)^d.l)⁻¹ • DebyeRadialTrace.angularToroidal P x)) 2‖ ≤ 2*M1*M2 :=
    cross_component_bound _ _ M1 M2 (h1 x hx0) (h2 x hx0)
  have hBn : ‖amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l ‖x‖/(‖x‖ : ℂ))‖ ≤
      ‖amplitude d‖*((d.l : ℝ)*(d.l+1))*2/‖x‖ := by
    rw [norm_mul,norm_mul,norm_mul,norm_div,hphase,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hrpos]
    have hl : ‖((d.l : ℂ)*(d.l+1))‖=(d.l : ℝ)*(d.l+1) := by
      rw [show ((d.l : ℂ)*(d.l+1))=(((d.l : ℝ)*(d.l+1) : ℝ) : ℂ) by push_cast; ring,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    rw [hl,mul_one]
    calc _ ≤ ‖amplitude d‖*((d.l : ℝ)*(d.l+1))*(2/‖x‖) := by gcongr
      _ = _ := by ring
  have hCn : ‖-I*amplitude d*phase d.l*p d.l ‖x‖‖ ≤ 2*‖amplitude d‖ := by
    rw [norm_mul,norm_mul,norm_mul,norm_neg,Complex.norm_I,hphase]
    nlinarith [mul_nonneg (norm_nonneg (amplitude d)) (sub_nonneg.2 hpb)]
  generalize Complex.exp (I*(‖x‖ : ℂ))*(‖x‖ : ℂ)⁻¹ = c at hcn ⊢
  generalize amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l ‖x‖/(‖x‖ : ℂ)) = B at hBn ⊢
  generalize -I*amplitude d*phase d.l*p d.l ‖x‖ = C0 at hCn ⊢
  generalize crossProduct (((‖x‖ : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.radial P x)
      (conjugate (((‖x‖ : ℂ)^d.l)⁻¹ • DebyeRadialTrace.angularToroidal P x)) 2 = X at hX1 ⊢
  have hL : 0 ≤ (d.l : ℝ)*(d.l+1) := by positivity
  simp only [norm_mul,hcj,hcn]
  calc _ ≤ ‖x‖⁻¹*‖x‖⁻¹*((‖amplitude d‖*((d.l : ℝ)*(d.l+1))*2/‖x‖)*(2*‖amplitude d‖)*(2*M1*M2)) := by
        gcongr
    _ = _ := by
      field_simp
      ring

end OQ14.SourceRemotePlaneFlux
#print axioms OQ14.SourceRemotePlaneFlux.toroidal_dot
#print axioms OQ14.SourceRemotePlaneFlux.poloidal_cross_zero
#print axioms OQ14.SourceRemotePlaneFlux.cross_smul
#print axioms OQ14.SourceRemotePlaneFlux.cross_add_smul
#print axioms OQ14.SourceRemotePlaneFlux.cross_component_bound
#print axioms OQ14.SourceRemotePlaneFlux.plane_flux_bound
