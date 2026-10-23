import DebyeMaxwell
import SphereMagneticParity

/-! Literal equator-even and half-turn-even scalar plane waves for the restricted TE interpolation route. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SymmetricScalarWaves
open Maxwell ModalDipole ExteriorHelmholtz ExteriorClassical
open scoped Topology

def linear (v : Fin 3 → ℝ) : Space →L[ℝ] ℝ := ∑ i, v i • EuclideanSpace.proj i

theorem linear_basis (v : Fin 3 → ℝ) (i : Fin 3) : linear v (basis i)=v i := by
  fin_cases i <;> simp [linear,Fin.sum_univ_three,basis,EuclideanSpace.single_apply]

def cosine (v : Fin 3 → ℝ) (x : Space) : ℂ := (Real.cos (linear v x) : ℂ)
def sine (v : Fin 3 → ℝ) (x : Space) : ℂ := (Real.sin (linear v x) : ℂ)

theorem cosine_smooth (v : Fin 3 → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cosine v) :=
  Complex.ofRealCLM.contDiff.comp ((linear v).contDiff.cos)

theorem cosine_partial (v : Fin 3 → ℝ) (x : Space) (i : Fin 3) :
    dcoord (cosine v) x i=-(v i : ℂ)*sine v x := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x
    ((Real.hasDerivAt_cos (linear v x)).comp_hasFDerivAt x (linear v).hasFDerivAt)
  have he := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hd.fderiv
  simpa [cosine,sine,dcoord,ContinuousLinearMap.comp_apply,linear_basis,smul_eq_mul,mul_comm] using he

theorem sine_partial (v : Fin 3 → ℝ) (x : Space) (i : Fin 3) :
    dcoord (sine v) x i=(v i : ℂ)*cosine v x := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x
    ((Real.hasDerivAt_sin (linear v x)).comp_hasFDerivAt x (linear v).hasFDerivAt)
  have he := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hd.fderiv
  simpa [cosine,sine,dcoord,ContinuousLinearMap.comp_apply,linear_basis,smul_eq_mul,mul_comm] using he

theorem cosine_second (v : Fin 3 → ℝ) (x : Space) (i : Fin 3) :
    dcoord (fun y => dcoord (cosine v) y i) x i=-(v i : ℂ)^2*cosine v x := by
  have hss : ContDiff ℝ (⊤ : ℕ∞) (sine v) :=
    Complex.ofRealCLM.contDiff.comp (linear v).contDiff.sin
  have hs : DifferentiableAt ℝ (sine v) x := hss.differentiable (by simp) x
  rw [show (fun y => dcoord (cosine v) y i)=(fun y => -(v i : ℂ)*sine v y) from funext (fun y => cosine_partial v y i)]
  rw [partial_const_mul hs,sine_partial]
  ring

def scalar (a b c : ℝ) (x : Space) : ℂ := cosine ![a,b,0] x*cosine ![0,0,c] x

theorem scalar_smooth (a b c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scalar a b c) :=
  (cosine_smooth ![a,b,0]).mul (cosine_smooth ![0,0,c])

theorem scalar_formula (a b c : ℝ) (x : Space) : scalar a b c x=
    ((Real.cos (a*x 0+b*x 1)*Real.cos (c*x 2) : ℝ) : ℂ) := by
  simp [scalar,cosine,linear,Fin.sum_univ_three,smul_eq_mul]

theorem equator_even (a b c : ℝ) (x : Space) :
    scalar a b c (SphereReactionKernel.reflect x)=scalar a b c x := by
  simp [scalar_formula,SphereReactionKernel.reflect,SphereReactionKernel.sign]

theorem half_turn_even (a b c : ℝ) (x : Space) :
    scalar a b c (-SphereReactionKernel.reflect x)=scalar a b c x := by
  simp only [scalar_formula,PiLp.neg_apply]
  have h0 : SphereReactionKernel.reflect x 0=x 0 := by simp [SphereReactionKernel.reflect,SphereReactionKernel.sign]
  have h1 : SphereReactionKernel.reflect x 1=x 1 := by simp [SphereReactionKernel.reflect,SphereReactionKernel.sign]
  have h2 : SphereReactionKernel.reflect x 2= -x 2 := by simp [SphereReactionKernel.reflect,SphereReactionKernel.sign]
  rw [h0,h1,h2]
  simp only [neg_neg,mul_neg,← neg_add,Real.cos_neg]

theorem helmholtz (a b c k : ℝ) (hdisp : a^2+b^2+c^2=k^2) (x : Space) :
    laplacian (scalar a b c) x+(k : ℂ)^2*scalar a b c x=0 := by
  have hh := (cosine_smooth ![a,b,0]).contDiffAt (x := x)
  have hv := (cosine_smooth ![0,0,c]).contDiffAt (x := x)
  unfold scalar laplacian
  simp only [Fin.sum_univ_three,
    HelmholtzTestCalculus.second_partial_mul _ _ x hh hv,cosine_second]
  simp only [cosine_partial]
  norm_num
  simp only [show (![0,0,c] : Fin 3 → ℝ) 2=c from rfl,
    show (![a,b,0] : Fin 3 → ℝ) 2=0 from rfl,Complex.ofReal_zero,zero_mul,mul_zero,zero_pow,neg_zero,add_zero]
  have hd : (a : ℂ)^2+(b : ℂ)^2+(c : ℂ)^2=(k : ℂ)^2 := by exact_mod_cast hdisp
  linear_combination -cosine ![a,b,0] x*cosine ![0,0,c] x*hd

theorem actual_te_maxwell (a b k : ℝ) (hk : k ≠ 0) (hfreq : a^2+b^2 ≤ k^2) (x : Space) :
    MaxwellAt k 1 1 (DebyeMaxwell.teElectric (scalar a b (Real.sqrt (k^2-a^2-b^2))))
      (DebyeMaxwell.teMagnetic k (scalar a b (Real.sqrt (k^2-a^2-b^2)))) x := by
  have hd : a^2+b^2+(Real.sqrt (k^2-a^2-b^2))^2=k^2 := by
    rw [Real.sq_sqrt (by linarith)]
    ring
  exact DebyeMaxwell.te_real_maxwell isOpen_univ _ (fun y _ => (scalar_smooth _ _ _).contDiffAt)
    k k 1 hk (by ring) (fun y _ => helmholtz a b _ k hd y) x (Set.mem_univ x)

end OQ14.SymmetricScalarWaves
#print axioms OQ14.SymmetricScalarWaves.linear_basis
#print axioms OQ14.SymmetricScalarWaves.cosine_smooth
#print axioms OQ14.SymmetricScalarWaves.cosine_partial
#print axioms OQ14.SymmetricScalarWaves.sine_partial
#print axioms OQ14.SymmetricScalarWaves.cosine_second
#print axioms OQ14.SymmetricScalarWaves.scalar_smooth
#print axioms OQ14.SymmetricScalarWaves.scalar_formula
#print axioms OQ14.SymmetricScalarWaves.equator_even
#print axioms OQ14.SymmetricScalarWaves.half_turn_even
#print axioms OQ14.SymmetricScalarWaves.helmholtz
#print axioms OQ14.SymmetricScalarWaves.actual_te_maxwell
