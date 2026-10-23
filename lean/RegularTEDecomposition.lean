import RegularTEIncoming
import RiccatiMaxwell

/-! Genuine electric and magnetic Hankel decomposition of a regular TE wave. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RegularTEDecomposition
open Complex Filter Set Maxwell ModalDipole ExteriorClassical HarmonicPolynomial
open RegularTEIncoming
open scoped Topology

theorem electric_split (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (x : Space) (hx : x≠0) :
    DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave l 1 p) x=electric l false p x+electric l true p x := by
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  let n : SphereReactionKernel.Sphere := ⟨‖x‖⁻¹ • x,by
    rw [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr),inv_mul_cancel₀ hr.ne']⟩
  have he : ‖x‖ • (n : Space)=x := by change ‖x‖ • (‖x‖⁻¹ • x)=x; rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  simpa only [he] using regular_split l p hp n ‖x‖ hr

theorem electric_smooth (l : ℕ) (inward : Bool) (p : Poly) (x : Space) (hx : x≠0) (j : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => electric l inward p y j) x := by
  have hs := RiccatiMaxwell.scalar_smooth l _ (profile_smooth l inward) p x hx
  exact contDiffAt_const.mul (DebyeCalculus.toroidal_smooth _ x hs j)

theorem magnetic_curl (l : ℕ) (inward : Bool) (p : Poly) (x : Space) (hx : x≠0) (j : Fin 3) :
    magnetic l inward p x j= -I*curl (electric l inward p) x j := by
  have hs := RiccatiMaxwell.scalar_smooth l _ (profile_smooth l inward) p x hx
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun y => RiccatiDebyeTrace.M l (radial l inward) p y i) x :=
    (DebyeCalculus.toroidal_smooth _ x hs i).differentiableAt (by simp)
  change magnetic l inward p x j= -I*curl (fun y i => (1/2 : ℂ)*RiccatiDebyeTrace.M l (radial l inward) p y i) x j
  rw [curl_const_mul _ x (1/2 : ℂ) hd]
  simp only [magnetic,RiccatiTransmission.teH,RiccatiTransmission.teE,RiccatiDebyeTrace.N,
    Pi.smul_apply,smul_eq_mul,div_one]
  ring

theorem magnetic_split (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (x : Space) (hx : x≠0) :
    DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave l 1 p) x=magnetic l false p x+magnetic l true p x := by
  have hn : {y : Space | y≠0}∈𝓝 x := isOpen_compl_singleton.mem_nhds hx
  have he : DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave l 1 p)=ᶠ[𝓝 x]
      (fun y => electric l false p y+electric l true p y) := by
    filter_upwards [hn] with y hy
    exact electric_split l p hp y hy
  have hc := curl_congr_nhds he
  change curl (DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave l 1 p)) x=
    curl (fun y j => electric l false p y j+electric l true p y j) x at hc
  rw [curl_add _ _ x (fun j => (electric_smooth l false p x hx j).differentiableAt (by simp))
    (fun j => (electric_smooth l true p x hx j).differentiableAt (by simp))] at hc
  ext j
  change (-I/1)*curl (DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave l 1 p)) x j=_
  rw [hc]
  simp only [Pi.add_apply,div_one,magnetic_curl l false p x hx j,magnetic_curl l true p x hx j]
  ring

end OQ14.RegularTEDecomposition
#print axioms OQ14.RegularTEDecomposition.electric_split
#print axioms OQ14.RegularTEDecomposition.electric_smooth
#print axioms OQ14.RegularTEDecomposition.magnetic_curl
#print axioms OQ14.RegularTEDecomposition.magnetic_split
