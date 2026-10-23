import RestrictedTEAsymptotics
import RestrictedTEStaticFlux
import StaticPlaneDipoleError

/-! Actual harmonic magnetic pairing of the proved static finite-ball dipole error. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEDipoleError
open Complex MeasureTheory Metric Set Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology ComplexConjugate
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dipoleFlux (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (A : Index →₀ ℂ) (q : Plane) : ℂ :=
  crossProduct (FinitePlaneDipole.dipoles p r P (MaxwellPlaneTail.planePoint q))
    (conjugate (magnetic A (MaxwellPlaneTail.planePoint q))) 2

omit [Fintype ι] [DecidableEq ι] in
private theorem magnetic_scaled_bound (A : Index →₀ ℂ) (B : ℝ)
    (hb : ∀ x : Space, ∀ i : Fin 3, ‖magnetic A x i‖≤B) (a : ℝ) (ha : 0<a) (x : Space) (i : Fin 3) :
    ‖magnetic ((a : ℂ)⁻¹ • A) x i‖≤B/a := by
  rw [RestrictedTEScale.magnetic_smul,Pi.smul_apply,Pi.smul_apply,norm_smul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha]
  exact (mul_le_mul_of_nonneg_left (hb x i) (inv_nonneg.mpr ha.le)).trans_eq (by ring)

theorem from_estimates (A : Index →₀ ℂ) : ∃ B : ℝ, 0≤B ∧ ∀ (p : ι → Space)
    (ρ a χ δ R k b U V γ : ℝ) (hρ : 0<ρ) (ha : 0<a) (hχ : 0≤χ) (hγ : 0<γ),
    (∀ l, (γ+ρ)*a≤|p l 2|) →
    ∀ (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
      (f : VectorFourier.VectorL2) (E : ι → Vector),
      FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b U V hχ d f E →
      let S := DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
        (ParityMaterialField.solution d k (b/a) f)
      let P := fun l => StaticSpherePolarization.polarization χ (E l)
      Integrable (fun q : Plane => staticMixed S ((a : ℂ)⁻¹ • A) q-
        dipoleFlux p (fun _ => ρ*a) P ((a : ℂ)⁻¹ • A) q) ∧
      (∫ q : Plane, ‖staticMixed S ((a : ℂ)⁻¹ • A) q-
        dipoleFlux p (fun _ => ρ*a) P ((a : ℂ)⁻¹ • A) q‖)≤
          (6*B*|StaticPlaneInclusions.errorConstant (ι := ι) χ ρ δ k R b U V γ|)*a := by
  obtain ⟨B,hB,hH⟩ := RestrictedTEMagnetic.magnetic_bounded A
  refine ⟨B,hB,?_⟩
  intro p ρ a χ δ R k b U V γ hρ ha hχ hγ hh d f E he
  let S := DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
    (ParityMaterialField.solution d k (b/a) f)
  let P := fun l => StaticSpherePolarization.polarization χ (E l)
  let F := fun q i => NewtonSeparatedResponse.response S (MaxwellPlaneTail.planePoint q) i-
    FinitePlaneDipole.dipoles p (fun _ => ρ*a) P (MaxwellPlaneTail.planePoint q) i
  let D := |StaticPlaneInclusions.errorConstant (ι := ι) χ ρ δ k R b U V γ|
  have hf (i : Fin 3) := StaticPlaneDipoleError.inverse_from_estimates p ρ a χ δ R k b U V γ
    hρ ha hχ hγ hh d f E he i
  have hbF (i : Fin 3) : (∫ q : Plane, ‖F q i‖)≤3*D*a^2 :=
    (hf i).2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)) (sq_nonneg a))
  have hmag (q : Plane) (i : Fin 3) : ‖magnetic ((a : ℂ)⁻¹ • A) (MaxwellPlaneTail.planePoint q) i‖≤B/a :=
    magnetic_scaled_bound A B hH a ha _ i
  let G := fun q : Plane => crossProduct (F q) (conjugate (magnetic ((a : ℂ)⁻¹ • A) (MaxwellPlaneTail.planePoint q))) 2
  have hm (i : Fin 3) := (RestrictedTEMagnetic.magnetic_continuous ((a : ℂ)⁻¹ • A) i).comp MaxwellPlaneTail.planePoint_continuous
  have hgm : AEStronglyMeasurable G :=
    ((hf 0).1.aestronglyMeasurable.mul (hm 1).star.aestronglyMeasurable).sub
      ((hf 1).1.aestronglyMeasurable.mul (hm 0).star.aestronglyMeasurable)
  have hbG (q : Plane) : ‖G q‖≤(B/a)*(‖F q 0‖+‖F q 1‖) := by
    change ‖F q 0*star (magnetic ((a : ℂ)⁻¹ • A) (MaxwellPlaneTail.planePoint q) 1)-
      F q 1*star (magnetic ((a : ℂ)⁻¹ • A) (MaxwellPlaneTail.planePoint q) 0)‖≤_
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_star]
    exact (add_le_add
      (mul_le_mul_of_nonneg_left (hmag q 1) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hmag q 0) (norm_nonneg _))).trans_eq (by ring)
  have hg := ((hf 0).1.norm.add (hf 1).1.norm).const_mul (B/a)
  have hi := hg.mono' hgm (Filter.Eventually.of_forall hbG)
  have hfun : (fun q : Plane => staticMixed S ((a : ℂ)⁻¹ • A) q-
      dipoleFlux p (fun _ => ρ*a) P ((a : ℂ)⁻¹ • A) q)=G := by
    funext q
    simp [staticMixed,dipoleFlux,G,F,cross_apply,conjugate]
    ring
  change Integrable (fun q : Plane => staticMixed S ((a : ℂ)⁻¹ • A) q-dipoleFlux p (fun _ => ρ*a) P ((a : ℂ)⁻¹ • A) q) ∧ _
  rw [hfun]
  refine ⟨hi,?_⟩
  calc
    _ = ∫ q : Plane, ‖G q‖ := integral_congr_ae
      (Filter.Eventually.of_forall (fun q => congrArg norm (congrFun hfun q)))
    _ ≤ ∫ q : Plane, (B/a)*(‖F q 0‖+‖F q 1‖) := integral_mono_ae hi.norm hg (Filter.Eventually.of_forall hbG)
    _ = (B/a)*((∫ q : Plane, ‖F q 0‖)+(∫ q : Plane, ‖F q 1‖)) := by
      rw [integral_const_mul,integral_add (hf 0).1.norm (hf 1).1.norm]
    _ ≤ (B/a)*(3*D*a^2+3*D*a^2) := mul_le_mul_of_nonneg_left (add_le_add (hbF 0) (hbF 1)) (by positivity)
    _ = _ := by change _=(6*B*D)*a; field_simp [ha.ne']; ring

end OQ14.RestrictedTEDipoleError
#print axioms OQ14.RestrictedTEDipoleError.from_estimates
