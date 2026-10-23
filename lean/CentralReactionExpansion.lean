import DebyeUnitReaction
import SolidWaveParity
import RadialVectorParity

/-! Central-inversion projections of the actual J kernel and actual pair-stack limiting source series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CentralReactionExpansion
open Complex OQ14.Maxwell OQ14.VectorHarmonicNormalization OQ14.DebyeUnitReaction
  OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit

abbrev Mode := Sum PositiveIndex PositiveIndex

def dyad (x y : Space) (i j : Fin 3) : Mode → ℂ := Sum.elim
  (fun a => weight a*electric a x i*electric a y j)
  (fun a => weight a*toroidal a x i*toroidal a y j)

def inversionSign : Mode → ℂ := Sum.elim
  (fun a => (-1 : ℂ)^(a.1+2)) (fun a => (-1 : ℂ)^(a.1+1))

theorem dyad_inversion (x y : Space) (i j : Fin 3) (m : Mode) :
    dyad x (-y) i j m=inversionSign m*dyad x y i j m := by
  cases m with
  | inl a =>
    have hp := SolidWaveParity.electric_parity (a.1+1) 1
      (SphereHarmonicBasis.representative (a.1+1) a.2)
      (SphereHarmonicBasis.representative_homogeneous (a.1+1) a.2) y j
    change electric a (-y) j=(-1 : ℂ)^(a.1+1+1)*electric a y j at hp
    simp only [dyad,inversionSign,Sum.elim_inl,hp]
    ring
  | inr a =>
    have hp := SolidWaveParity.toroidal_parity (a.1+1) 1
      (SphereHarmonicBasis.representative (a.1+1) a.2)
      (SphereHarmonicBasis.representative_homogeneous (a.1+1) a.2) y j
    change toroidal a (-y) j=(-1 : ℂ)^(a.1+1)*toroidal a y j at hp
    simp only [dyad,inversionSign,Sum.elim_inr,hp]
    ring

def evenKernel (x y : Space) (i j : Fin 3) : ℂ :=
  (SphereReactionKernel.J 1 (x-y) i j+SphereReactionKernel.J 1 (x-(-y)) i j)/2
def oddKernel (x y : Space) (i j : Fin 3) : ℂ :=
  (SphereReactionKernel.J 1 (x-y) i j-SphereReactionKernel.J 1 (x-(-y)) i j)/2

theorem even_expansion (x y : Space) (i j : Fin 3) :
    HasSum (fun m => (1+inversionSign m)*dyad x y i j m/2) (evenKernel x y i j) := by
  have h := ((J_unit_expansion x y i j).add (J_unit_expansion x (-y) i j)).div_const 2
  change HasSum (fun m => (dyad x y i j m+dyad x (-y) i j m)/2) _ at h
  convert h using 1
  funext m
  rw [dyad_inversion]
  ring

theorem odd_expansion (x y : Space) (i j : Fin 3) :
    HasSum (fun m => (1-inversionSign m)*dyad x y i j m/2) (oddKernel x y i j) := by
  have h := ((J_unit_expansion x y i j).sub (J_unit_expansion x (-y) i j)).div_const 2
  change HasSum (fun m => (dyad x y i j m-dyad x (-y) i j m)/2) _ at h
  convert h using 1
  funext m
  rw [dyad_inversion]
  ring

def sourceFactor (q : ℝ) (hq : 0<q) (n : ℕ) : Mode → ℂ := Sum.elim
  (fun a => -((limitingCoefficients (a.1+1) (pairs q (q^2) hq (sq_pos_of_pos hq) n)).1/
    (limitingCoefficients (a.1+1) (pairs q (q^2) hq (sq_pos_of_pos hq) n)).2+I))
  (fun a => -((limitingCoefficients (a.1+1) (pairs q 1 hq zero_lt_one n)).1/
    (limitingCoefficients (a.1+1) (pairs q 1 hq zero_lt_one n)).2+I))

theorem sourceFactor_parity (q : ℝ) (hq : 0<q) (n : ℕ) (m : Mode) :
    sourceFactor q hq n m=I*((((q^(2*n) : ℝ) : ℂ)-1)*(1+inversionSign m)/2+
      ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*(1-inversionSign m)/2) := by
  cases m with
  | inl a =>
    simpa only [sourceFactor,Sum.elim_inl,RadialVectorParity.parityFactor,inversionSign,
      if_true,Nat.add_assoc] using RadialVectorParity.tm_parity q hq n (a.1+1)
  | inr a =>
    simpa only [sourceFactor,Sum.elim_inr,RadialVectorParity.parityFactor,inversionSign,
      Bool.false_eq_true,if_false,Nat.add_zero] using RadialVectorParity.te_parity q hq n (a.1+1)

theorem pair_reaction_expansion (q : ℝ) (hq : 0<q) (n : ℕ) (x y : Space) (i j : Fin 3) :
    HasSum (fun m => sourceFactor q hq n m*dyad x y i j m)
      (I*((((q^(2*n) : ℝ) : ℂ)-1)*evenKernel x y i j+
        ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*oddKernel x y i j)) := by
  have he := (even_expansion x y i j).mul_left ((((q^(2*n) : ℝ) : ℂ)-1))
  have ho := (odd_expansion x y i j).mul_left (((((q^(2*n))⁻¹ : ℝ) : ℂ)-1))
  have h := (he.add ho).mul_left I
  convert h using 1
  funext m
  rw [sourceFactor_parity]
  ring

end OQ14.CentralReactionExpansion

#print axioms OQ14.CentralReactionExpansion.dyad_inversion
#print axioms OQ14.CentralReactionExpansion.even_expansion
#print axioms OQ14.CentralReactionExpansion.odd_expansion
#print axioms OQ14.CentralReactionExpansion.sourceFactor_parity
#print axioms OQ14.CentralReactionExpansion.pair_reaction_expansion
