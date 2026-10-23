import OutgoingSpatialSeries
import RadialLayerMaxwell

/-! Actual vacuum source profiles are smooth Debye waves on punctured space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VacuumOutgoingHelmholtz
open Set Filter Complex OQ14.Maxwell OQ14.HarmonicPolynomial
open OQ14.RiccatiDebyeTrace OQ14.DebyeCalculus OQ14.DebyeRadialTrace
open scoped Topology

def u (l : ℕ) : ℝ → ℂ := RadialLayer.value l 1 1 (-I) 1
def uD (l : ℕ) : ℝ → ℂ := RadialLayer.momentum l 1 1 (-I) 1

theorem u_value (l : ℕ) (r : ℝ) : u l r= -I*ModalAlgebra.xi l r := by
  have he : ModalAlgebra.xi l r=(HankelRealBasis.regular l r : ℂ)+I*(HankelRealBasis.irregular l r : ℂ) := by
    simpa only [HankelRealBasis.regular,HankelRealBasis.irregular,mul_comm] using
      (Complex.re_add_im (ModalAlgebra.xi l r)).symm
  simp only [u,RadialLayer.value,RadialLayer.fa,RadialLayer.fb,one_mul,one_div,one_mul,mul_one,
    Complex.ofReal_mul,Complex.ofReal_one]
  rw [he]
  ring_nf
  simp [I_sq]

theorem uD_value (l : ℕ) (r : ℝ) : uD l r= -I*ModalAlgebra.xiD l r := by
  have he : ModalAlgebra.xiD l r=(HankelRealBasis.regularD l r : ℂ)+I*(HankelRealBasis.irregularD l r : ℂ) := by
    simpa only [HankelRealBasis.regularD,HankelRealBasis.irregularD,mul_comm] using
      (Complex.re_add_im (ModalAlgebra.xiD l r)).symm
  simp only [uD,RadialLayer.momentum,RadialLayer.fc,RadialLayer.fd,one_mul,one_div,mul_one,
    Complex.ofReal_mul,Complex.ofReal_one]
  rw [he]
  ring_nf
  simp [I_sq]

theorem u_hasDerivAt (l : ℕ) (r : ℝ) (hr : r≠0) : HasDerivAt (u l) (uD l r) r := by
  simpa only [u,uD,Complex.ofReal_one,one_mul] using
    (RadialLayer.solution_ode l 1 1 (-I) 1 r one_ne_zero one_ne_zero hr).1

theorem profile_smooth (l : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l (u l)) (Ioi 0) :=
  RadialLayerMaxwell.profile_smooth l 1 1 (-I) 1 one_ne_zero

theorem raw_state (l : ℕ) (r : ℝ) :
    SourceRadialSystem.raw (VacuumOutgoingBounds.data l) r=(u l r,uD l r) := by
  have h := SourceCoreReaction.vacuum_raw (VacuumOutgoingBounds.data l) r
  have he : SourceCoreReaction.vacuum (VacuumOutgoingBounds.data l)=VacuumOutgoingBounds.data l := rfl
  rw [he] at h
  rw [h,u_value,uD_value]
  rfl

theorem inverse_sigma (l : ℕ) (r : ℝ) :
    SourceRadialSystem.inverseSigma (VacuumOutgoingBounds.data l) r=1 := by
  simp only [SourceRadialSystem.inverseSigma,SourceRadialSystem.extend,VacuumOutgoingBounds.data]
  split_ifs <;> simp_all

theorem N_profile (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x≠0) (i : Fin 3) :
    N l (u l) p x i=(uD l ‖x‖/(‖x‖ : ℂ)^l)*dcoord (complexEvaluate p) x i+
      ((l : ℂ)*(l+1)*u l ‖x‖/(‖x‖ : ℂ)^(l+3)-
        (l : ℂ)*uD l ‖x‖/(‖x‖ : ℂ)^(l+2))*(x i : ℂ)*complexEvaluate p x := by
  have hr : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  change curl (toroidal (scalar (RadialQuotient.profile l (u l)) p)) x i=_
  rw [toroidal_curl _ (profile_smooth l) p l hp hh x hx i,
    (RadialQuotient.profile_hasDerivAt l (u l) (uD l) ‖x‖ (norm_ne_zero_iff.mpr hx)
      (u_hasDerivAt l ‖x‖ (norm_ne_zero_iff.mpr hx))).deriv]
  simp only [RadialQuotient.profile,RadialQuotient.profileD,pow_succ,Nat.cast_add,Nat.cast_one]
  generalize he : (‖x‖ : ℂ)^l=z
  have hz : z≠0 := he ▸ pow_ne_zero l hr
  field_simp [hr,hz]
  ring_nf
  field_simp [hr,hz]
  ring

theorem electric_profile (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x≠0) :
    SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) p x=N l (u l) p x := by
  ext i
  rw [N_profile l p hp hh x hx i]
  simp only [SourceUnclippedMaxwell.electric,raw_state,inverse_sigma,one_mul]
  rfl

theorem magnetic_profile (l : ℕ) (p : Poly) (x : Space) (hx : x≠0) :
    SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) p x=fun i => -I*M l (u l) p x i := by
  ext i
  rw [M_components l (u l) (profile_smooth l) p x hx i]
  simp only [SourceUnclippedMaxwell.magnetic,raw_state,show (VacuumOutgoingBounds.data l).l=l from rfl]
  ring


theorem M_smooth (l : ℕ) (p : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => M l (u l) p y i) x :=
  toroidal_smooth _ x (RiccatiMaxwell.scalar_smooth l (u l) (profile_smooth l) p x hx) i

theorem N_smooth (l : ℕ) (p : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => N l (u l) p y i) x :=
  ExteriorClassical.curl_smooth _ (M_smooth l p x hx) i

theorem electric_smooth (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x≠0) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) p y i) x := by
  apply (N_smooth l p x hx i).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact congrFun (electric_profile l p hp hh y hy) i

theorem magnetic_smooth (l : ℕ) (p : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) p y i) x := by
  apply (contDiffAt_const.mul (M_smooth l p x hx i)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact congrFun (magnetic_profile l p y hy) i

theorem M_helmholtz (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x≠0) (i : Fin 3) :
    ExteriorHelmholtz.laplacian (fun y => M l (u l) p y i) x+M l (u l) p x i=0 := by
  have h := toroidal_helmholtz isOpen_compl_singleton
    (scalar (RadialQuotient.profile l (u l)) p)
    (fun y hy => RiccatiMaxwell.scalar_smooth l (u l) (profile_smooth l) p y hy) 1
    (fun y hy => RadialLayerMaxwell.scalar_helmholtz l 1 1 (-I) 1 one_ne_zero one_ne_zero p hp hh y hy)
    x hx i
  simpa only [one_pow,one_mul] using h

theorem N_helmholtz (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x≠0) (i : Fin 3) :
    ExteriorHelmholtz.laplacian (fun y => N l (u l) p y i) x+N l (u l) p x i=0 := by
  rw [N,laplacian_curl _ x (M_smooth l p x hx)]
  have he : curl (fun y j => ExteriorHelmholtz.laplacian (fun z => M l (u l) p z j) y) x=
      curl (fun y j => -1*M l (u l) p y j) x := by
    apply curl_congr
    intro j
    filter_upwards [eventually_ne_nhds hx] with y hy
    linear_combination M_helmholtz l p hp hh y hy j
  rw [he,Maxwell.curl_const_mul _ x (-1) (fun j => (M_smooth l p x hx j).differentiableAt (by simp))]
  change -1*N l (u l) p x i+N l (u l) p x i=0
  ring

theorem electric_helmholtz (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x≠0) (i : Fin 3) :
    ExteriorHelmholtz.laplacian (fun y => SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) p y i) x+
      SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) p x i=0 := by
  have he : (fun y => SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) p y i)=ᶠ[𝓝 x]
      (fun y => N l (u l) p y i) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact congrFun (electric_profile l p hp hh y hy) i
  rw [ExteriorGreen.laplacian_congr_nhds he,he.eq_of_nhds]
  exact N_helmholtz l p hp hh x hx i

theorem magnetic_helmholtz (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x≠0) (i : Fin 3) :
    ExteriorHelmholtz.laplacian (fun y => SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) p y i) x+
      SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) p x i=0 := by
  have he : (fun y => SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) p y i)=ᶠ[𝓝 x]
      (fun y => -I*M l (u l) p y i) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact congrFun (magnetic_profile l p y hy) i
  rw [ExteriorGreen.laplacian_congr_nhds he,he.eq_of_nhds,
    HelmholtzTestCalculus.laplacian_mul (fun _ => -I) _ x contDiffAt_const (M_smooth l p x hx i)]
  simp only [ExteriorHelmholtz.laplacian,dcoord,fderiv_const,ContinuousLinearMap.zero_apply,Pi.zero_apply,mul_zero,
    Finset.sum_const_zero,zero_add,add_zero,zero_mul]
  change -I*ExteriorHelmholtz.laplacian (fun y => M l (u l) p y i) x+ -I*M l (u l) p x i=0
  linear_combination -I*M_helmholtz l p hp hh x hx i
end OQ14.VacuumOutgoingHelmholtz





#print axioms OQ14.VacuumOutgoingHelmholtz.u_value
#print axioms OQ14.VacuumOutgoingHelmholtz.uD_value
#print axioms OQ14.VacuumOutgoingHelmholtz.u_hasDerivAt
#print axioms OQ14.VacuumOutgoingHelmholtz.profile_smooth
#print axioms OQ14.VacuumOutgoingHelmholtz.raw_state
#print axioms OQ14.VacuumOutgoingHelmholtz.inverse_sigma
#print axioms OQ14.VacuumOutgoingHelmholtz.N_profile
#print axioms OQ14.VacuumOutgoingHelmholtz.electric_profile
#print axioms OQ14.VacuumOutgoingHelmholtz.magnetic_profile
#print axioms OQ14.VacuumOutgoingHelmholtz.M_smooth
#print axioms OQ14.VacuumOutgoingHelmholtz.N_smooth
#print axioms OQ14.VacuumOutgoingHelmholtz.electric_smooth
#print axioms OQ14.VacuumOutgoingHelmholtz.magnetic_smooth
#print axioms OQ14.VacuumOutgoingHelmholtz.M_helmholtz
#print axioms OQ14.VacuumOutgoingHelmholtz.N_helmholtz
#print axioms OQ14.VacuumOutgoingHelmholtz.electric_helmholtz
#print axioms OQ14.VacuumOutgoingHelmholtz.magnetic_helmholtz
