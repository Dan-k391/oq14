import ConePowerPrimitive

/-! Literal variation-of-constants particular solution of the forced cone equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.ConicalRadialParticular
open MeasureTheory Set OQ14.ConePowerPrimitive
open scoped Topology

def power (β r : ℝ) : ℂ := ((r^β : ℝ) : ℂ)

theorem power_mul (α β r : ℝ) (hr : 0 < r) : power α r*power β r=power (α+β) r := by
  simp only [power,← Complex.ofReal_mul,Real.rpow_add hr]

theorem power_hasDerivAt (β r : ℝ) (hr : 0 < r) :
    HasDerivAt (power β) ((β : ℂ)*power (β-1) r) r := by
  have hc : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 (r^β) := by
    simpa using (Complex.ofRealCLM.hasFDerivAt (x := r^β)).hasDerivAt
  convert hc.scomp r (Real.hasDerivAt_rpow_const (p := β) (Or.inl hr.ne')) using 1
  simp only [power,Complex.real_smul,Complex.ofReal_mul,mul_one]

def minusForcing (ν : ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ := B r-((ν+1 : ℝ) : ℂ)*A r
def plusForcing (ν : ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ := B r+(ν : ℂ)*A r

def leftPrimitive (ν : ℝ) (A B : ℝ → ℂ) : ℝ → ℂ := primitive (-ν) (minusForcing ν A B)
def rightPrimitive (ν : ℝ) (A B : ℝ → ℂ) : ℝ → ℂ := primitive (ν+1) (plusForcing ν A B)

def particular (ν : ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ :=
  (power ν r*leftPrimitive ν A B r-power (-ν-1) r*rightPrimitive ν A B r)/((2*ν+1 : ℝ) : ℂ)

def flux (ν : ℝ) (A B : ℝ → ℂ) (r : ℝ) : ℂ :=
  ((ν : ℂ)*(power (ν+1) r*leftPrimitive ν A B r)+
    ((ν+1 : ℝ) : ℂ)*(power (-ν) r*rightPrimitive ν A B r))/((2*ν+1 : ℝ) : ℂ)

theorem primitive_derivatives (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0)) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (leftPrimitive ν A B) (power (-ν) r*minusForcing ν A B r) r ∧
      HasDerivAt (rightPrimitive ν A B) (power (ν+1) r*plusForcing ν A B r) r := by
  exact ⟨primitive_hasDerivAt (-ν) (by linarith [hν.2]) _
    (hB.sub (continuousOn_const.mul hA)) r hr,
    primitive_hasDerivAt (ν+1) (by linarith [hν.1]) _
    (hB.add (continuousOn_const.mul hA)) r hr⟩

theorem particular_hasDerivAt (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0)) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (particular ν A B) (flux ν A B r/(r : ℂ)^2-A r) r := by
  obtain ⟨hL,hR⟩ := primitive_derivatives ν hν A B hA hB r hr
  have h := (((power_hasDerivAt ν r hr).mul hL).sub
    ((power_hasDerivAt (-ν-1) r hr).mul hR)).div_const (((2*ν+1 : ℝ) : ℂ))
  have hden : (((2*ν+1 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hν.1])
  have hrC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have h1 : power ν r*power (-ν) r=1 := by rw [power_mul _ _ _ hr]; simp [power]
  have h2 : power (-ν-1) r*power (ν+1) r=1 := by
    rw [power_mul _ _ _ hr,show -ν-1+(ν+1)=0 by ring]; simp [power]
  have h3 : power (ν+1) r=(r : ℂ)^2*power (ν-1) r := by
    rw [show (r : ℂ)^2=power 2 r by simp [power],power_mul _ _ _ hr]
    congr 1
    ring
  have h4 : power (-ν) r=(r : ℂ)^2*power (-ν-1-1) r := by
    rw [show (r : ℂ)^2=power 2 r by simp [power],power_mul _ _ _ hr]
    congr 1
    ring
  have hD : 1+(ν : ℂ)*2 ≠ 0 := by
    convert hden using 1
    push_cast
    ring
  have hDr : (ν : ℂ)*(r : ℂ)^2*2+(r : ℂ)^2 ≠ 0 := by
    convert mul_ne_zero hD (pow_ne_zero 2 hrC) using 1
    ring
  convert h using 1
  dsimp only [particular,flux,minusForcing,plusForcing]
  simp only [mul_assoc,← mul_assoc (power ν r) (power (-ν) r),h1,
    ← mul_assoc (power (-ν-1) r) (power (ν+1) r),h2,one_mul]
  rw [h3,h4]
  push_cast
  ring_nf
  field_simp [hD,hDr]
  ring

theorem flux_hasDerivAt (ν : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0)) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (flux ν A B) (((ν*(ν+1) : ℝ) : ℂ)*particular ν A B r+(r : ℂ)*B r) r := by
  obtain ⟨hL,hR⟩ := primitive_derivatives ν hν A B hA hB r hr
  have h := ((((power_hasDerivAt (ν+1) r hr).mul hL).const_mul (ν : ℂ)).add
    (((power_hasDerivAt (-ν) r hr).mul hR).const_mul (((ν+1 : ℝ) : ℂ)))).div_const (((2*ν+1 : ℝ) : ℂ))
  have hden : (((2*ν+1 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hν.1])
  have h1 : power (ν+1) r*power (-ν) r=(r : ℂ) := by
    rw [power_mul _ _ _ hr,show ν+1+-ν=1 by ring]; simp [power]
  have h2 : power (-ν) r*power (ν+1) r=(r : ℂ) := by rw [mul_comm,h1]
  have hD : 1+(ν : ℂ)*2 ≠ 0 := by
    convert hden using 1
    push_cast
    ring
  convert h using 1
  dsimp only [flux,particular,minusForcing,plusForcing]
  simp only [show ν+1-1=ν by ring]
  simp only [mul_assoc,← mul_assoc (power (ν+1) r) (power (-ν) r),h1,
    ← mul_assoc (power (-ν) r) (power (ν+1) r),h2]
  push_cast
  ring_nf
  field_simp [hD]
  ring

end OQ14.ConicalRadialParticular

#print axioms OQ14.ConicalRadialParticular.power_mul
#print axioms OQ14.ConicalRadialParticular.power_hasDerivAt
#print axioms OQ14.ConicalRadialParticular.primitive_derivatives
#print axioms OQ14.ConicalRadialParticular.particular_hasDerivAt
#print axioms OQ14.ConicalRadialParticular.flux_hasDerivAt
