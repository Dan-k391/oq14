import ConicalRungeClosure

/-! The literal transverse functions used in the Runge span are actual entire vacuum Maxwell waves. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalPlaneWaves
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalRungeAnnihilator OQ14.ConicalRungeBall
open scoped InnerProductSpace ComplexConjugate Topology
abbrev Space := Maxwell.Space

def direction (n : Space) : Vector := fun j => (n j : ℂ)
def waveVector (k : ℝ) (n : Space) : Vector := fun j => -Complex.I*k*(n j : ℂ)
def polarization (n : Space) (i : Fin 3) : Vector := fun j => DyadicRadiation.transverse n i j
def magneticPolarization (n : Space) (i : Fin 3) : Vector := -crossProduct (direction n) (polarization n i)
def electric (k : ℝ) (n : Space) (i : Fin 3) : Field := exponentialField (waveVector k n) (polarization n i)
def magnetic (k : ℝ) (n : Space) (i : Fin 3) : Field := exponentialField (waveVector k n) (magneticPolarization n i)

theorem linearPhase_eq (k : ℝ) (n x : Space) :
    linearPhase (waveVector k n) x= -Complex.I*k*(@inner ℝ Space _ n x : ℝ) := by
  have hi : @inner ℝ Space _ n x=n 0*x 0+n 1*x 1+n 2*x 2 := by
    simp only [PiLp.inner_apply,Fin.sum_univ_three,RCLike.inner_apply,conj_trivial]
    ring
  rw [hi]
  change (-Complex.I*(k : ℂ)*(n 0 : ℂ))*(x 0 : ℂ)+
    (-Complex.I*(k : ℂ)*(n 1 : ℂ))*(x 1 : ℂ)+
    (-Complex.I*(k : ℂ)*(n 2 : ℂ))*(x 2 : ℂ)=_
  push_cast
  ring

theorem electric_eq_waveValue (k : ℝ) (n : Space) (i j : Fin 3) (x : Space) :
    electric k n i x j=waveValue k n i j x := by
  simp only [electric,exponentialField,exponential,linearPhase_eq,waveValue,phase,polarization]
  ring

theorem direction_norm_sq (n : Space) (hn : ‖n‖=1) :
    (n 0 : ℂ)^2+(n 1 : ℂ)^2+(n 2 : ℂ)^2=1 := by
  have hr : n 0^2+n 1^2+n 2^2=(1 : ℝ) := by
    simpa only [PiLp.inner_apply,Fin.sum_univ_three,RCLike.inner_apply,conj_trivial,hn,one_pow,pow_two,mul_one]
      using real_inner_self_eq_norm_sq n
  exact_mod_cast hr

theorem polarization_eq (n : Space) (hn : ‖n‖=1) (i j : Fin 3) :
    polarization n i j=(if i=j then 1 else 0)-(n i : ℂ)*(n j : ℂ) := by
  simp only [polarization,DyadicRadiation.transverse,GreenKernel.unitCoordinate,hn,Complex.ofReal_one,div_one]

theorem polarization_tangent (n : Space) (hn : ‖n‖=1) (i : Fin 3) :
    dot (direction n) (polarization n i)=0 := by
  have h := direction_norm_sq n hn
  fin_cases i
  · simp [dot,direction,polarization_eq n hn]
    linear_combination -(n 0 : ℂ)*h
  · simp [dot,direction,polarization_eq n hn]
    linear_combination -(n 1 : ℂ)*h
  · simp [dot,direction,polarization_eq n hn]
    linear_combination -(n 2 : ℂ)*h

theorem amplitude_curls (k : ℝ) (n : Space) (hn : ‖n‖=1) (i : Fin 3) :
    crossProduct (waveVector k n) (polarization n i)=(fun j => Complex.I*k*1*magneticPolarization n i j) ∧
    crossProduct (waveVector k n) (magneticPolarization n i)=(fun j => -Complex.I*k*1*polarization n i j) := by
  have hs := direction_norm_sq n hn
  have ht := polarization_tangent n hn i
  constructor
  · ext j
    fin_cases j <;> simp [waveVector,magneticPolarization,direction,cross_apply] <;> ring
  · simp only [dot,direction] at ht
    ext j
    fin_cases j
    · simp [waveVector,magneticPolarization,direction,cross_apply]
      linear_combination -Complex.I*(k : ℂ)*(polarization n i 0)*hs+Complex.I*(k : ℂ)*(n 0 : ℂ)*ht
    · simp [waveVector,magneticPolarization,direction,cross_apply]
      linear_combination -Complex.I*(k : ℂ)*(polarization n i 1)*hs+Complex.I*(k : ℂ)*(n 1 : ℂ)*ht
    · simp [waveVector,magneticPolarization,direction,cross_apply]
      linear_combination -Complex.I*(k : ℂ)*(polarization n i 2)*hs+Complex.I*(k : ℂ)*(n 2 : ℂ)*ht

theorem maxwell_at (k : ℝ) (n : Space) (hn : ‖n‖=1) (i : Fin 3) (x : Space) :
    MaxwellAt k 1 1 (electric k n i) (magnetic k n i) x := by
  exact exponential_maxwell (waveVector k n) (polarization n i) (magneticPolarization n i) k 1 1
    (amplitude_curls k n hn i).1 (amplitude_curls k n hn i).2 x

theorem electric_smooth (k : ℝ) (n : Space) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => electric k n i x j) := by
  unfold electric exponentialField exponential
  exact contDiff_const.mul ((linearPhase (waveVector k n)).contDiff.cexp)

theorem magnetic_smooth (k : ℝ) (n : Space) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => magnetic k n i x j) := by
  unfold magnetic exponentialField exponential
  exact contDiff_const.mul ((linearPhase (waveVector k n)).contDiff.cexp)

end OQ14.ConicalPlaneWaves

#print axioms OQ14.ConicalPlaneWaves.linearPhase_eq
#print axioms OQ14.ConicalPlaneWaves.electric_eq_waveValue
#print axioms OQ14.ConicalPlaneWaves.direction_norm_sq
#print axioms OQ14.ConicalPlaneWaves.polarization_eq
#print axioms OQ14.ConicalPlaneWaves.polarization_tangent
#print axioms OQ14.ConicalPlaneWaves.amplitude_curls
#print axioms OQ14.ConicalPlaneWaves.maxwell_at
#print axioms OQ14.ConicalPlaneWaves.electric_smooth
#print axioms OQ14.ConicalPlaneWaves.magnetic_smooth
