import ShellInclusionAlgebra

/-! Named shell, combined, effective and inverse blocks in an arbitrary ring. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ShellInclusionBlocks
open OQ14.ShellInclusionAlgebra

variable {R : Type*} [Ring R]

/-- The shell block. -/
def shell (Ss T : R) : R := 1-Ss*T*Ss

/-- The combined block of shell plus inclusion. -/
def combined (Ss Si T : R) : R := 1-(Ss+Si)*T*(Ss+Si)

/-- The effective inclusion block. -/
def effective (Ss Si T : R) : R := 1-Si*green Ss T*Si

/-- The explicit inverse of the combined block. -/
def combinedInverse (Ss Si T : R) : R :=
  1+(Ss+Si)*(green Ss T*(Ss+Si)+green Ss T*Si*Ring.inverse (effective Ss Si T)*Si*green Ss T*(Ss+Si))

theorem effective_mul (Ss Si T : R) (hs : IsUnit (shell Ss T)) (hsi : Ss*Si=0) (his : Si*Ss=0) :
    effective Ss Si T*(Si*T*(Ss+Si))=(Si*green Ss T*(Ss+Si))*combined Ss Si T :=
  effective_of_combined_unit Ss Si T hs hsi his

theorem combined_isUnit (Ss Si T : R) (hs : IsUnit (shell Ss T)) (hsi : Ss*Si=0) (his : Si*Ss=0)
    (hE : IsUnit (effective Ss Si T)) : IsUnit (combined Ss Si T) :=
  ShellInclusionAlgebra.combined_isUnit Ss Si T hs hsi his hE

theorem combined_inverse (Ss Si T : R) (hs : IsUnit (shell Ss T)) (hsi : Ss*Si=0) (his : Si*Ss=0)
    (hE : IsUnit (effective Ss Si T)) : Ring.inverse (combined Ss Si T)=combinedInverse Ss Si T :=
  ShellInclusionAlgebra.combined_inverse Ss Si T hs hsi his hE

end OQ14.ShellInclusionBlocks
#print axioms OQ14.ShellInclusionBlocks.effective_mul
#print axioms OQ14.ShellInclusionBlocks.combined_isUnit
#print axioms OQ14.ShellInclusionBlocks.combined_inverse
