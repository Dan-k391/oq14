import Packet05GraphWeakDivergence
import Packet05GraphChartMatrix

/-! Pointwise constitutive identity: covariant gradient plus Piola flux yields
exactly the anisotropic graph metric, with arbitrary complex permittivity. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
namespace OQ14.Packet05GraphConstitutive
open OQ14.Packet05GraphChartMatrix

def pulledGradient (a b : ℝ) (u : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![u 0+(a : ℂ)*u 2, u 1+(b : ℂ)*u 2, u 2]

def piolaScalarFlux (a b : ℝ) (ε : ℂ) (u : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![ε*u 0, ε*u 1, ε*(u 2-(a : ℂ)*u 0-(b : ℂ)*u 1)]

theorem transformed_scalar_flux (a b : ℝ) (ε : ℂ) (u : Fin 3 → ℂ) (i : Fin 3) :
    piolaScalarFlux a b ε u i = ε * ∑ j : Fin 3, (metric a b i j : ℂ) * pulledGradient a b u j := by
  fin_cases i <;> simp [piolaScalarFlux, pulledGradient, metric, Fin.sum_univ_three,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow] <;> ring_nf <;> simp

end OQ14.Packet05GraphConstitutive
#print axioms OQ14.Packet05GraphConstitutive.transformed_scalar_flux
