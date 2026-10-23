import VacuumOutgoingHelmholtz

/-! Genuine smooth Helmholtz finite partial sums of the actual outgoing spatial series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.OutgoingFiniteHelmholtz
open Set OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.DebyeCalculus
open OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization OQ14.OutgoingSpatialSeries

theorem laplacian_const_mul (c : ℂ) (f : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) : laplacian (fun y => c*f y) x=c*laplacian f x := by
  rw [HelmholtzTestCalculus.laplacian_mul (fun _ => c) f x contDiffAt_const hf]
  simp [laplacian,dcoord]

theorem linear_helmholtz (c d : ℂ) (f g : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (hF : laplacian f x+f x=0) (hG : laplacian g x+g x=0) :
    laplacian (fun y => c*f y+d*g y) x+(c*f x+d*g x)=0 := by
  have he : (fun y => c*f y+d*g y)=(fun y => c*f y-(-d)*g y) := by funext y;ring
  rw [he,laplacian_sub _ _ x (contDiffAt_const.mul hf) (contDiffAt_const.mul hg),
    laplacian_const_mul c f x hf,laplacian_const_mul (-d) g x hg]
  linear_combination c*hF+d*hG

theorem finite_helmholtz {ι : Type*} (s : Finset ι) (f : ι → Space → ℂ) (x : Space)
    (hf : ∀ a∈s,ContDiffAt ℝ (⊤ : ℕ∞) (f a) x)
    (heq : ∀ a∈s,laplacian (f a) x+f a x=0) :
    laplacian (fun y => ∑ a∈s,f a y) x+(∑ a∈s,f a x)=0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [laplacian,dcoord]
  | @insert a s ha ih =>
    have hs := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
      (fun b hb => heq b (Finset.mem_insert_of_mem hb))
    simpa only [Finset.sum_insert ha,one_mul] using
      linear_helmholtz 1 1 (f a) (fun y => ∑ b∈s,f b y) x (hf a (Finset.mem_insert_self a s))
        (ContDiffAt.sum (fun b hb => hf b (Finset.mem_insert_of_mem hb)))
        (heq a (Finset.mem_insert_self a s)) hs

theorem term_smooth (a : PositiveIndex) (y : Space) (i j : Fin 3) (x : Space) (hx : x≠0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => term a z y i j) x :=
  (contDiffAt_const.mul (VacuumOutgoingHelmholtz.electric_smooth (a.1+1) _
    (representative_homogeneous _ _) (representative_harmonic _ _) x hx i)).add
    (contDiffAt_const.mul (VacuumOutgoingHelmholtz.magnetic_smooth (a.1+1) _ x hx i))

theorem term_helmholtz (a : PositiveIndex) (y : Space) (i j : Fin 3) (x : Space) (hx : x≠0) :
    laplacian (fun z => term a z y i j) x+term a x y i j=0 :=
  linear_helmholtz _ _ _ _ x
    (VacuumOutgoingHelmholtz.electric_smooth (a.1+1) _
      (representative_homogeneous _ _) (representative_harmonic _ _) x hx i)
    (VacuumOutgoingHelmholtz.magnetic_smooth (a.1+1) _ x hx i)
    (VacuumOutgoingHelmholtz.electric_helmholtz (a.1+1) _
      (representative_homogeneous _ _) (representative_harmonic _ _) x hx i)
    (VacuumOutgoingHelmholtz.magnetic_helmholtz (a.1+1) _
      (representative_homogeneous _ _) (representative_harmonic _ _) x hx i)

theorem partial_sum_smooth (s : Finset PositiveIndex) (y : Space) (i j : Fin 3) (x : Space) (hx : x≠0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => ∑ a∈s,term a z y i j) x :=
  ContDiffAt.sum (fun a _ => term_smooth a y i j x hx)

theorem partial_sum_helmholtz (s : Finset PositiveIndex) (y : Space) (i j : Fin 3) (x : Space) (hx : x≠0) :
    laplacian (fun z => ∑ a∈s,term a z y i j) x+(∑ a∈s,term a x y i j)=0 :=
  finite_helmholtz s _ x (fun a _ => term_smooth a y i j x hx)
    (fun a _ => term_helmholtz a y i j x hx)

end OQ14.OutgoingFiniteHelmholtz
#print axioms OQ14.OutgoingFiniteHelmholtz.laplacian_const_mul
#print axioms OQ14.OutgoingFiniteHelmholtz.linear_helmholtz
#print axioms OQ14.OutgoingFiniteHelmholtz.finite_helmholtz
#print axioms OQ14.OutgoingFiniteHelmholtz.term_smooth
#print axioms OQ14.OutgoingFiniteHelmholtz.term_helmholtz
#print axioms OQ14.OutgoingFiniteHelmholtz.partial_sum_smooth
#print axioms OQ14.OutgoingFiniteHelmholtz.partial_sum_helmholtz
