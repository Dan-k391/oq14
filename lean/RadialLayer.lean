import HankelPositive

/-! Actual homogeneous radial layers and their determinant-one transfers. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000

namespace OQ14.RadialLayer

open OQ14.RadialGreen OQ14.HankelRealBasis OQ14.HankelEnergy

def potential (l : ℕ) (q σ x : ℝ) : ℝ := angular l/(σ*x^2)-q^2/σ
def fa (l : ℕ) (q x : ℝ) : ℝ := regular l (q*x)
def fb (l : ℕ) (q σ x : ℝ) : ℝ := (σ/q)*irregular l (q*x)
def fc (l : ℕ) (q σ x : ℝ) : ℝ := (q/σ)*regularD l (q*x)
def fd (l : ℕ) (q x : ℝ) : ℝ := irregularD l (q*x)

theorem basis_determinant (l : ℕ) (q σ x : ℝ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hx : x ≠ 0) :
    fa l q x*fd l q x-fb l q σ x*fc l q σ x = 1 := by
  have h := real_wronskian l (q*x) (mul_ne_zero hq hx)
  dsimp only [fa,fb,fc,fd]
  field_simp
  linear_combination (q*σ)*h

def basis (l : ℕ) (q σ x : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) (hx : x ≠ 0) : RealTransfer where
  a := fa l q x
  b := fb l q σ x
  c := fc l q σ x
  d := fd l q x
  det_one := basis_determinant l q σ x hq hσ hx

theorem basis_ode (l : ℕ) (q σ x : ℝ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fa l q) (σ*fc l q σ x) x ∧
    HasDerivAt (fb l q σ) (σ*fd l q x) x ∧
    HasDerivAt (fc l q σ) (potential l q σ x*fa l q x) x ∧
    HasDerivAt (fd l q) (potential l q σ x*fb l q σ x) x := by
  obtain ⟨ha,hb⟩ := real_basis_hasDerivAt l (q*x) (mul_ne_zero hq hx)
  obtain ⟨hc,hd⟩ := real_basis_ode l (q*x) (mul_ne_zero hq hx)
  have harg := (hasDerivAt_id x).const_mul q
  refine ⟨?_,?_,?_,?_⟩
  · convert ha.comp x harg using 1
    dsimp only [fc]
    field_simp
    ring
  · convert (hb.comp x harg).const_mul (σ/q) using 1
    dsimp only [fd]
    field_simp
    ring
  · convert (hc.comp x harg).const_mul (q/σ) using 1
    dsimp only [potential,fa,weight]
    field_simp
    ring
  · convert hd.comp x harg using 1
    dsimp only [potential,fb,weight]
    field_simp
    ring

def inverse (m : RealTransfer) : RealTransfer where
  a := m.d
  b := -m.b
  c := -m.c
  d := m.a
  det_one := by nlinarith [m.det_one]

def compose (m n : RealTransfer) : RealTransfer where
  a := m.a*n.a+m.b*n.c
  b := m.a*n.b+m.b*n.d
  c := m.c*n.a+m.d*n.c
  d := m.c*n.b+m.d*n.d
  det_one := by
    calc
      _ = (m.a*m.d-m.b*m.c)*(n.a*n.d-n.b*n.c) := by ring
      _ = 1 := by rw [m.det_one,n.det_one]; ring

def transfer (l : ℕ) (q σ a b : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) : RealTransfer :=
  compose (basis l q σ b hq hσ hb) (inverse (basis l q σ a hq hσ ha))

def value (l : ℕ) (q σ : ℝ) (α β : ℂ) (x : ℝ) : ℂ :=
  (fa l q x : ℂ)*α+(fb l q σ x : ℂ)*β
def momentum (l : ℕ) (q σ : ℝ) (α β : ℂ) (x : ℝ) : ℂ :=
  (fc l q σ x : ℂ)*α+(fd l q x : ℂ)*β

theorem solution_ode (l : ℕ) (q σ : ℝ) (α β : ℂ) (x : ℝ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (value l q σ α β) ((σ : ℂ)*momentum l q σ α β x) x ∧
    HasDerivAt (momentum l q σ α β) ((potential l q σ x : ℂ)*value l q σ α β x) x := by
  obtain ⟨ha,hb,hc,hd⟩ := basis_ode l q σ x hq hσ hx
  constructor
  · convert (ha.ofReal_comp.mul_const α).add (hb.ofReal_comp.mul_const β) using 1
    simp only [momentum,Complex.ofReal_mul]
    ring
  · convert (hc.ofReal_comp.mul_const α).add (hd.ofReal_comp.mul_const β) using 1
    simp only [value,Complex.ofReal_mul]
    ring

def initialAlpha (l : ℕ) (q σ a : ℝ) (u p : ℂ) : ℂ :=
  (fd l q a : ℂ)*u-(fb l q σ a : ℂ)*p
def initialBeta (l : ℕ) (q σ a : ℝ) (u p : ℂ) : ℂ :=
  -(fc l q σ a : ℂ)*u+(fa l q a : ℂ)*p

theorem initial_value (l : ℕ) (q σ a : ℝ) (u p : ℂ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (ha : a ≠ 0) :
    value l q σ (initialAlpha l q σ a u p) (initialBeta l q σ a u p) a = u := by
  have h : (fa l q a : ℂ)*fd l q a-(fb l q σ a : ℂ)*fc l q σ a=1 := by
    exact_mod_cast basis_determinant l q σ a hq hσ ha
  dsimp only [value,initialAlpha,initialBeta]
  linear_combination u*h

theorem initial_momentum (l : ℕ) (q σ a : ℝ) (u p : ℂ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (ha : a ≠ 0) :
    momentum l q σ (initialAlpha l q σ a u p) (initialBeta l q σ a u p) a = p := by
  have h : (fa l q a : ℂ)*fd l q a-(fb l q σ a : ℂ)*fc l q σ a=1 := by
    exact_mod_cast basis_determinant l q σ a hq hσ ha
  dsimp only [momentum,initialAlpha,initialBeta]
  linear_combination p*h

theorem transfer_value (l : ℕ) (q σ a b : ℝ) (u p : ℂ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    value l q σ (initialAlpha l q σ a u p) (initialBeta l q σ a u p) b =
      ((transfer l q σ a b hq hσ ha hb).a : ℂ)*u+
      ((transfer l q σ a b hq hσ ha hb).b : ℂ)*p := by
  simp only [value,initialAlpha,initialBeta,transfer,compose,inverse,basis,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

theorem transfer_momentum (l : ℕ) (q σ a b : ℝ) (u p : ℂ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    momentum l q σ (initialAlpha l q σ a u p) (initialBeta l q σ a u p) b =
      ((transfer l q σ a b hq hσ ha hb).c : ℂ)*u+
      ((transfer l q σ a b hq hσ ha hb).d : ℂ)*p := by
  simp only [momentum,initialAlpha,initialBeta,transfer,compose,inverse,basis,
    Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_neg]
  ring

end OQ14.RadialLayer

#print axioms OQ14.RadialLayer.basis_determinant
#print axioms OQ14.RadialLayer.basis_ode
#print axioms OQ14.RadialLayer.solution_ode
#print axioms OQ14.RadialLayer.initial_value
#print axioms OQ14.RadialLayer.initial_momentum
#print axioms OQ14.RadialLayer.transfer_value
#print axioms OQ14.RadialLayer.transfer_momentum
