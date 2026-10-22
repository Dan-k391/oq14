import RiccatiMaxwell
import RadialLayer

/-! Actual all-degree Maxwell solutions for the explicit homogeneous layer basis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.RadialLayerMaxwell
open Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.RadialLayer
  OQ14.HankelRealBasis OQ14.ModalAlgebra OQ14.RiccatiTransmission

theorem value_smooth (l : ℕ) (q σ : ℝ) (α β : ℂ) (hq : q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (value l q σ α β) (Ioi 0) := by
  have hd : DifferentiableOn ℂ (xi l) ({0}ᶜ : Set ℂ) :=
    fun z hz => (xi_hasDerivAt l z hz).differentiableAt.differentiableWithinAt
  have hs : ContDiffOn ℂ (⊤ : ℕ∞) (xi l) ({0}ᶜ : Set ℂ) := hd.contDiffOn isOpen_compl_singleton
  intro r hr
  have hqr : ((q*r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (mul_ne_zero hq hr.ne')
  have hx : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => xi l ((q*s : ℝ) : ℂ)) r :=
    ((hs.contDiffAt (isOpen_compl_singleton.mem_nhds hqr)).restrict_scalars ℝ).comp r
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hreg : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => (regular l (q*s) : ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp r (Complex.reCLM.contDiff.contDiffAt.comp r hx)
  have hirreg : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => (irregular l (q*s) : ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp r (Complex.imCLM.contDiff.contDiffAt.comp r hx)
  have hv : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (regular l (q*s) : ℂ)*α+((σ/q : ℝ) : ℂ)*(irregular l (q*s) : ℂ)*β) r :=
    (hreg.mul contDiffAt_const).add ((contDiffAt_const.mul hirreg).mul contDiffAt_const)
  change ContDiffWithinAt ℝ (⊤ : ℕ∞)
    (fun s : ℝ => (fa l q s : ℂ)*α+(fb l q σ s : ℂ)*β) (Ioi 0) r
  simpa only [fa,fb,Complex.ofReal_mul] using hv.contDiffWithinAt

theorem profile_smooth (l : ℕ) (q σ : ℝ) (α β : ℂ) (hq : q ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (RadialQuotient.profile l (value l q σ α β)) (Ioi 0) := by
  intro r hr
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simpa only [RadialQuotient.profile,div_eq_mul_inv] using
    (((value_smooth l q σ α β hq).contDiffAt (isOpen_Ioi.mem_nhds hr)).mul
      ((Complex.ofRealCLM.contDiff.pow (l+1)).contDiffAt.inv (pow_ne_zero _ hrc))).contDiffWithinAt

theorem value_second (l : ℕ) (q σ : ℝ) (α β : ℂ) (hq : q ≠ 0) (hσ : σ ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s => (σ : ℂ)*momentum l q σ α β s)
      (((l : ℂ)*(l+1)/(r : ℂ)^2-(q : ℂ)^2)*value l q σ α β r) r := by
  have he : (((l : ℂ)*(l+1)/(r : ℂ)^2-(q : ℂ)^2)*value l q σ α β r)=
      (σ : ℂ)*((potential l q σ r : ℂ)*value l q σ α β r) := by
    simp only [potential,HankelEnergy.angular,Complex.ofReal_sub,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one]
    field_simp [Complex.ofReal_ne_zero.mpr hσ,Complex.ofReal_ne_zero.mpr hr.ne']
    ring
  rw [he]
  exact ((solution_ode l q σ α β r hq hσ hr.ne').2).const_mul (σ : ℂ)

theorem scalar_helmholtz (l : ℕ) (q σ : ℝ) (α β : ℂ) (hq : q ≠ 0) (hσ : σ ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    ExteriorHelmholtz.laplacian
      (DebyeRadialTrace.scalar (RadialQuotient.profile l (value l q σ α β)) p) x+
      (q : ℂ)^2*DebyeRadialTrace.scalar (RadialQuotient.profile l (value l q σ α β)) p x=0 :=
  RiccatiMaxwell.scalar_helmholtz l _ (fun s => (σ : ℂ)*momentum l q σ α β s) q
    (profile_smooth l q σ α β hq)
    (fun r hr => (solution_ode l q σ α β r hq hσ hr.ne').1)
    (value_second l q σ α β hq hσ) p hp hh x hx

theorem te_maxwell (l : ℕ) (q σ k ε : ℝ) (α β : ℂ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hk : k ≠ 0) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    MaxwellAt k 1 ε (teE l (value l q σ α β) p) (teH l k (value l q σ α β) p) x :=
  RiccatiMaxwell.te_real_maxwell l _ (fun s => (σ : ℂ)*momentum l q σ α β s) q k ε hk hdisp
    (profile_smooth l q σ α β hq)
    (fun r hr => (solution_ode l q σ α β r hq hσ hr.ne').1)
    (value_second l q σ α β hq hσ) p hp hh x hx

theorem tm_maxwell (l : ℕ) (q σ k ε : ℝ) (α β : ℂ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hε : ε ≠ 0) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    MaxwellAt k 1 ε (tmE l ε (value l q σ α β) p) (tmH l k (value l q σ α β) p) x :=
  RiccatiMaxwell.tm_real_maxwell l _ (fun s => (σ : ℂ)*momentum l q σ α β s) q k ε hε hdisp
    (profile_smooth l q σ α β hq)
    (fun r hr => (solution_ode l q σ α β r hq hσ hr.ne').1)
    (value_second l q σ α β hq hσ) p hp hh x hx

end OQ14.RadialLayerMaxwell

#print axioms OQ14.RadialLayerMaxwell.value_smooth
#print axioms OQ14.RadialLayerMaxwell.profile_smooth
#print axioms OQ14.RadialLayerMaxwell.value_second
#print axioms OQ14.RadialLayerMaxwell.scalar_helmholtz
#print axioms OQ14.RadialLayerMaxwell.te_maxwell
#print axioms OQ14.RadialLayerMaxwell.tm_maxwell
