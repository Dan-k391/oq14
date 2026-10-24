import RestrictedTEDipoleError
import RestrictedTEDipoleLimit
import RestrictedTEPolarization
import RestrictedTESourceMass
import RestrictedTETotalFlux
import RestrictedTEDatumLinear
import MaterialSourceLinear

/-! Complex linearity in the coefficient vector of the actual complete harmonic TE parity total fields on the
observation plane, derived from the linearity of the actual material solution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTETotalLinear
open Complex MeasureTheory Metric Set Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
abbrev Space := FourierL2.Space

/-- Pointwise action of a linear combination on the coordinate functions of a source. -/
theorem source_comb_apply (ρ σ : Source) (z : ℂ) (j : Fin 3) (y : Space) :
    (ρ+z • σ) j y=ρ j y+z*σ j y := rfl

theorem admissible_comb (R d : ℝ) (ρ σ : Source) (z : ℂ)
    (hρ : Admissible R d ρ) (hσ : Admissible R d σ) : Admissible R d (ρ+z • σ) := by
  refine ⟨fun j => (hρ.integrable j).add ((hσ.integrable j).const_mul z),?_,?_⟩
  · intro j y hy
    rw [source_comb_apply,hρ.support j y hy,hσ.support j y hy]
    simp
  · intro j y hy
    by_cases h : ρ j y=0
    · have hn : σ j y≠0 := by
        intro hs
        apply hy
        rw [source_comb_apply,h,hs]
        simp
      exact hσ.gap j y hn
    · exact hρ.gap j y h

/-! ### Almost-everywhere independence of the representative -/

theorem response_congr (K : Space → ℂ) (ρ σ : Space → ℂ) (h : ρ =ᵐ[volume] σ) (x : Space) :
    KernelConvolution.response K ρ x=KernelConvolution.response K σ x := by
  unfold KernelConvolution.response
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem ext_electric_congr (k : ℝ) (ρ σ : Source) (h : ∀ j, ρ j =ᵐ[volume] σ j) (x : Space) :
    ExteriorContinuity.electric k ρ x=ExteriorContinuity.electric k σ x := by
  funext i
  unfold ExteriorContinuity.electric
  exact Finset.sum_congr rfl (fun j _ => response_congr _ _ _ (h j) x)

theorem ext_magnetic_congr (k : ℝ) (ρ σ : Source) (h : ∀ j, ρ j =ᵐ[volume] σ j) (x : Space) :
    MagneticResponse.magnetic k ρ x=MagneticResponse.magnetic k σ x := by
  funext i
  unfold MagneticResponse.magnetic
  rw [response_congr _ _ _ (h (WeakCurl.previous i)) x,response_congr _ _ _ (h (WeakCurl.next i)) x]

theorem parity_electric_congr (e : Bool) (k : ℝ) (ρ σ : Source) (h : ∀ j, ρ j =ᵐ[volume] σ j) (x : Space) :
    ParityPlaneFields.electric e k ρ x=ParityPlaneFields.electric e k σ x := by
  funext i
  unfold ParityPlaneFields.electric
  refine Finset.sum_congr rfl (fun j _ => ?_)
  apply integral_congr_ae
  filter_upwards [h j] with y hy
  rw [hy]

theorem parity_magnetic_congr (e : Bool) (k : ℝ) (ρ σ : Source) (h : ∀ j, ρ j =ᵐ[volume] σ j) (x : Space) :
    ParityPlaneFields.magnetic e k ρ x=ParityPlaneFields.magnetic e k σ x := by
  funext i
  unfold ParityPlaneFields.magnetic
  refine Finset.sum_congr rfl (fun j _ => ?_)
  apply integral_congr_ae
  filter_upwards [h j] with y hy
  rw [hy]

theorem total_electric_congr (k B : ℝ) (ρ σ : Source) (h : ∀ j, ρ j =ᵐ[volume] σ j) (inc : Field) (x : Space) :
    ParityPlaneFields.totalElectric k B ρ inc x=ParityPlaneFields.totalElectric k B σ inc x := by
  funext i
  unfold ParityPlaneFields.totalElectric
  rw [ext_electric_congr k ρ σ h x,parity_electric_congr true k ρ σ h x,parity_electric_congr false k ρ σ h x]

theorem total_magnetic_congr (k B : ℝ) (ρ σ : Source) (h : ∀ j, ρ j =ᵐ[volume] σ j) (inc : Field) (x : Space) :
    ParityPlaneFields.totalMagnetic k B ρ inc x=ParityPlaneFields.totalMagnetic k B σ inc x := by
  funext i
  unfold ParityPlaneFields.totalMagnetic
  rw [ext_magnetic_congr k ρ σ h x,parity_magnetic_congr true k ρ σ h x,parity_magnetic_congr false k ρ σ h x]

/-! ### Linear combinations of admissible sources -/

theorem response_comb (K : Space → ℂ) (f g : Space → ℂ) (z : ℂ) (x : Space)
    (hf : Integrable (fun y => f y*K (x-y))) (hg : Integrable (fun y => g y*K (x-y))) :
    KernelConvolution.response K (fun y => f y+z*g y) x=
      KernelConvolution.response K f x+z*KernelConvolution.response K g x := by
  unfold KernelConvolution.response
  have : (fun y => (f y+z*g y)*K (x-y))=fun y => f y*K (x-y)+z*(g y*K (x-y)) := by
    funext y
    ring
  rw [this,integral_add hf (hg.const_mul z),integral_const_mul]

theorem ext_electric_comb (k R d : ℝ) (hd : 0<d) (ρ σ : Source) (hρ : Admissible R d ρ)
    (hσ : Admissible R d σ) (z : ℂ) (q : Plane) :
    ExteriorContinuity.electric k (ρ+z • σ) (MaxwellPlaneTail.planePoint q)=
      ExteriorContinuity.electric k ρ (MaxwellPlaneTail.planePoint q)+
        z • ExteriorContinuity.electric k σ (MaxwellPlaneTail.planePoint q) := by
  funext i
  simp only [ExteriorContinuity.electric,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact response_comb _ (ρ j) (σ j) z _
    (response_plane_integrable _ (dyadic_measurable k i j)
      (fun w hw => ExteriorContinuity.dyadic_continuousAt k i j w hw) R d hd ρ hρ q j)
    (response_plane_integrable _ (dyadic_measurable k i j)
      (fun w hw => ExteriorContinuity.dyadic_continuousAt k i j w hw) R d hd σ hσ q j)

theorem ext_magnetic_comb (k R d : ℝ) (hd : 0<d) (ρ σ : Source) (hρ : Admissible R d ρ)
    (hσ : Admissible R d σ) (z : ℂ) (q : Plane) :
    MagneticResponse.magnetic k (ρ+z • σ) (MaxwellPlaneTail.planePoint q)=
      MagneticResponse.magnetic k ρ (MaxwellPlaneTail.planePoint q)+
        z • MagneticResponse.magnetic k σ (MaxwellPlaneTail.planePoint q) := by
  funext i
  have h1 (l m : Fin 3) := response_plane_integrable (fun w => GreenKernel.phiGradient k w m)
    (KernelGradient.gradient_measurable k m)
    (fun w hw => (KernelGradient.gradient_differentiableAt k m w hw).continuousAt) R d hd ρ hρ q l
  have h2 (l m : Fin 3) := response_plane_integrable (fun w => GreenKernel.phiGradient k w m)
    (KernelGradient.gradient_measurable k m)
    (fun w hw => (KernelGradient.gradient_differentiableAt k m w hw).continuousAt) R d hd σ hσ q l
  have c1 := response_comb (fun w => GreenKernel.phiGradient k w (WeakCurl.next i)) (ρ (WeakCurl.previous i))
    (σ (WeakCurl.previous i)) z (MaxwellPlaneTail.planePoint q) (h1 _ _) (h2 _ _)
  have c2 := response_comb (fun w => GreenKernel.phiGradient k w (WeakCurl.previous i)) (ρ (WeakCurl.next i))
    (σ (WeakCurl.next i)) z (MaxwellPlaneTail.planePoint q) (h1 _ _) (h2 _ _)
  simp only [MagneticResponse.magnetic,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change -(Complex.I*(k : ℂ))*(KernelConvolution.response _ (fun y => ρ (WeakCurl.previous i) y+z*σ (WeakCurl.previous i) y) _-
    KernelConvolution.response _ (fun y => ρ (WeakCurl.next i) y+z*σ (WeakCurl.next i) y) _)=_
  rw [c1,c2]
  ring

theorem parity_electric_comb (e : Bool) (k : ℝ) (ρ σ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hσ : ∀ j, Integrable (σ j)) (z : ℂ) (x : Space) :
    ParityPlaneFields.electric e k (ρ+z • σ) x=
      ParityPlaneFields.electric e k ρ x+z • ParityPlaneFields.electric e k σ x := by
  funext i
  simp only [ParityPlaneFields.electric,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 := ParityPlaneFields.electric_integrand e k ρ hρ x i j
  have h2 := ParityPlaneFields.electric_integrand e k σ hσ x i j
  have : (fun y => SphereReactionKernel.reaction e k x y i j*(ρ j y+z*σ j y))=
      fun y => SphereReactionKernel.reaction e k x y i j*ρ j y+
        z*(SphereReactionKernel.reaction e k x y i j*σ j y) := by
    funext y
    ring
  rw [this,integral_add h1 (h2.const_mul z),integral_const_mul]

theorem parity_magnetic_comb (e : Bool) (k : ℝ) (ρ σ : Source) (hρ : ∀ j, Integrable (ρ j))
    (hσ : ∀ j, Integrable (σ j)) (z : ℂ) (x : Space) :
    ParityPlaneFields.magnetic e k (ρ+z • σ) x=
      ParityPlaneFields.magnetic e k ρ x+z • ParityPlaneFields.magnetic e k σ x := by
  funext i
  simp only [ParityPlaneFields.magnetic,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have h1 := ParityPlaneFields.magnetic_integrand e k ρ hρ x i j
  have h2 := ParityPlaneFields.magnetic_integrand e k σ hσ x i j
  have : (fun y => SphereMagneticParity.magneticReaction e k x y i j*(ρ j y+z*σ j y))=
      fun y => SphereMagneticParity.magneticReaction e k x y i j*ρ j y+
        z*(SphereMagneticParity.magneticReaction e k x y i j*σ j y) := by
    funext y
    ring
  rw [this,integral_add h1 (h2.const_mul z),integral_const_mul]

theorem total_electric_comb (k B R d : ℝ) (hd : 0<d) (ρ σ : Source) (hρ : Admissible R d ρ)
    (hσ : Admissible R d σ) (z : ℂ) (e₁ e₂ : Field) (q : Plane) :
    ParityPlaneFields.totalElectric k B (ρ+z • σ) (e₁+z • e₂) (MaxwellPlaneTail.planePoint q)=
      ParityPlaneFields.totalElectric k B ρ e₁ (MaxwellPlaneTail.planePoint q)+
        z • ParityPlaneFields.totalElectric k B σ e₂ (MaxwellPlaneTail.planePoint q) := by
  funext i
  have h1 := congrFun (ext_electric_comb k R d hd ρ σ hρ hσ z q) i
  have h2 := congrFun (parity_electric_comb true k ρ σ hρ.integrable hσ.integrable z
    (MaxwellPlaneTail.planePoint q)) i
  have h3 := congrFun (parity_electric_comb false k ρ σ hρ.integrable hσ.integrable z
    (MaxwellPlaneTail.planePoint q)) i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h1 h2 h3 ⊢
  unfold ParityPlaneFields.totalElectric
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [h1,h2,h3]
  ring

theorem total_magnetic_comb (k B R d : ℝ) (hd : 0<d) (ρ σ : Source) (hρ : Admissible R d ρ)
    (hσ : Admissible R d σ) (z : ℂ) (e₁ e₂ : Field) (q : Plane) :
    ParityPlaneFields.totalMagnetic k B (ρ+z • σ) (e₁+z • e₂) (MaxwellPlaneTail.planePoint q)=
      ParityPlaneFields.totalMagnetic k B ρ e₁ (MaxwellPlaneTail.planePoint q)+
        z • ParityPlaneFields.totalMagnetic k B σ e₂ (MaxwellPlaneTail.planePoint q) := by
  funext i
  have h1 := congrFun (ext_magnetic_comb k R d hd ρ σ hρ hσ z q) i
  have h2 := congrFun (parity_magnetic_comb true k ρ σ hρ.integrable hσ.integrable z
    (MaxwellPlaneTail.planePoint q)) i
  have h3 := congrFun (parity_magnetic_comb false k ρ σ hρ.integrable hσ.integrable z
    (MaxwellPlaneTail.planePoint q)) i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h1 h2 h3 ⊢
  unfold ParityPlaneFields.totalMagnetic
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [h1,h2,h3]
  ring


/-! ### Generic reduction: a combination law gives a linear map -/

section Generic
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def linearOfComb (E : V → W) (h : ∀ (A B : V) (z : ℂ), E (A+z • B)=E A+z • E B) : V →ₗ[ℂ] W where
  toFun := E
  map_add' := fun A B => by simpa using h A B 1
  map_smul' := fun z A => by
    have h0 : E 0=0 := by
      have := h 0 0 1
      simpa using this
    simpa [h0] using h 0 A z

theorem linearOfComb_apply (E : V → W) (h : ∀ (A B : V) (z : ℂ), E (A+z • B)=E A+z • E B) (A : V) :
    linearOfComb E h A=E A := rfl

theorem cross_two (u v : Vector) : crossProduct u v 2=u 0*v 1-u 1*v 0 := by
  rw [cross_apply]
  rfl

theorem flux_sesq (E H : V →ₗ[ℂ] Vector) :
    OQ14.RestrictedTEPolarization.Sesq (fun A A' : V => crossProduct (E A) (conjugate (H A')) 2) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u u' v
    simp only [cross_two]
    simp only [map_add,conjugate,Pi.add_apply]
    ring
  · intro z u v
    simp only [cross_two]
    simp only [map_smul,conjugate,Pi.smul_apply,smul_eq_mul]
    ring
  · intro u v v'
    simp only [cross_two]
    simp only [map_add,conjugate,Pi.add_apply]
    ring
  · intro z u v
    simp only [cross_two]
    simp only [map_smul,conjugate,Pi.smul_apply,smul_eq_mul,map_mul]
    ring

section SesqAlgebra
open OQ14.RestrictedTEPolarization
open scoped ComplexConjugate
variable {B : V → V → W}

theorem sesq_zero_left (h : Sesq B) (u : V) : B 0 u=0 := by
  have := h.add_left 0 0 u
  simpa using this

theorem sesq_zero_right (h : Sesq B) (u : V) : B u 0=0 := by
  have := h.add_right u 0 0
  simpa using this

theorem sesq_sum_left (h : Sesq B) {κ : Type*} (s : Finset κ) (f : κ → V) (v : V) :
    B (∑ i ∈ s, f i) v=∑ i ∈ s, B (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesq_zero_left h]
  | insert i s hi ih => rw [Finset.sum_insert hi,h.add_left,ih,Finset.sum_insert hi]

theorem sesq_sum_right (h : Sesq B) {κ : Type*} (s : Finset κ) (u : V) (f : κ → V) :
    B u (∑ i ∈ s, f i)=∑ i ∈ s, B u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesq_zero_right h]
  | insert i s hi ih => rw [Finset.sum_insert hi,h.add_right,ih,Finset.sum_insert hi]

theorem sesq_expand (h : Sesq B) {κ : Type*} (s : Finset κ) (e : κ → V) (c d : κ → ℂ) :
    B (∑ i ∈ s, c i • e i) (∑ j ∈ s, d j • e j)=
      ∑ i ∈ s, ∑ j ∈ s, (c i*conj (d j)) • B (e i) (e j) := by
  rw [sesq_sum_left h]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [h.smul_left,sesq_sum_right h,Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [h.smul_right,smul_smul]

theorem sesq_sub {B₁ B₂ : V → V → W} (h₁ : Sesq B₁) (h₂ : Sesq B₂) :
    Sesq (fun u v => B₁ u v-B₂ u v) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u u' v
    simp only [h₁.add_left,h₂.add_left]
    abel
  · intro z u v
    simp only [h₁.smul_left,h₂.smul_left,smul_sub]
  · intro u v v'
    simp only [h₁.add_right,h₂.add_right]
    abel
  · intro z u v
    simp only [h₁.smul_right,h₂.smul_right,smul_sub]

end SesqAlgebra

end Generic

/-! ### Whole-plane L1 mass algebra for sesquilinear expansions -/

section Mass
open scoped ComplexConjugate
variable {κ : Type*}

theorem entry_bound (F1 F2 F3 F4 : Plane → ℂ) (h1 : Integrable F1) (h2 : Integrable F2)
    (h3 : Integrable F3) (h4 : Integrable F4) :
    Integrable (fun q => (1/4 : ℂ)*((F1 q-F2 q)+I*(F3 q-F4 q))) ∧
      (∫ q : Plane, ‖(1/4 : ℂ)*((F1 q-F2 q)+I*(F3 q-F4 q))‖)≤
        (1/4)*((∫ q : Plane, ‖F1 q‖)+(∫ q : Plane, ‖F2 q‖)+(∫ q : Plane, ‖F3 q‖)+
          (∫ q : Plane, ‖F4 q‖)) := by
  have hint : Integrable (fun q : Plane => (1/4 : ℂ)*((F1 q-F2 q)+I*(F3 q-F4 q))) :=
    ((h1.sub h2).add ((h3.sub h4).const_mul I)).const_mul _
  refine ⟨hint,?_⟩
  have hg : Integrable (fun q : Plane => (1/4 : ℝ)*(‖F1 q‖+‖F2 q‖+‖F3 q‖+‖F4 q‖)) :=
    (((h1.norm.add h2.norm).add h3.norm).add h4.norm).const_mul _
  have hle : (∫ q : Plane, ‖(1/4 : ℂ)*((F1 q-F2 q)+I*(F3 q-F4 q))‖)≤
      ∫ q : Plane, (1/4 : ℝ)*(‖F1 q‖+‖F2 q‖+‖F3 q‖+‖F4 q‖) := by
    apply integral_mono hint.norm hg
    intro q
    show ‖(1/4 : ℂ)*((F1 q-F2 q)+I*(F3 q-F4 q))‖≤(1/4 : ℝ)*(‖F1 q‖+‖F2 q‖+‖F3 q‖+‖F4 q‖)
    rw [norm_mul]
    have h14 : ‖(1/4 : ℂ)‖=1/4 := by norm_num
    rw [h14]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc ‖(F1 q-F2 q)+I*(F3 q-F4 q)‖≤‖F1 q-F2 q‖+‖I*(F3 q-F4 q)‖ := norm_add_le _ _
      _ ≤ (‖F1 q‖+‖F2 q‖)+(‖F3 q‖+‖F4 q‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
        exact add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
      _ = ‖F1 q‖+‖F2 q‖+‖F3 q‖+‖F4 q‖ := by ring
  refine hle.trans (le_of_eq ?_)
  have h12 : Integrable (fun q : Plane => ‖F1 q‖+‖F2 q‖) := h1.norm.add h2.norm
  have h123 : Integrable (fun q : Plane => ‖F1 q‖+‖F2 q‖+‖F3 q‖) := (h1.norm.add h2.norm).add h3.norm
  rw [integral_const_mul,integral_add h123 h4.norm,integral_add h12 h3.norm,integral_add h1.norm h2.norm]

theorem double_sum_bound (s : Finset κ) (M : κ → κ → Plane → ℂ)
    (hM : ∀ i ∈ s, ∀ j ∈ s, Integrable (M i j)) (c : κ → ℂ) (hc : ∀ i, ‖c i‖≤1) :
    Integrable (fun q : Plane => ∑ i ∈ s, ∑ j ∈ s, (c i*conj (c j))*M i j q) ∧
      (∫ q : Plane, ‖∑ i ∈ s, ∑ j ∈ s, (c i*conj (c j))*M i j q‖)≤
        ∑ i ∈ s, ∑ j ∈ s, ∫ q : Plane, ‖M i j q‖ := by
  have hint : Integrable (fun q : Plane => ∑ i ∈ s, ∑ j ∈ s, (c i*conj (c j))*M i j q) :=
    integrable_finset_sum _ (fun i hi => integrable_finset_sum _
      (fun j hj => (hM i hi j hj).const_mul _))
  refine ⟨hint,?_⟩
  have hg : Integrable (fun q : Plane => ∑ i ∈ s, ∑ j ∈ s, ‖M i j q‖) :=
    integrable_finset_sum _ (fun i hi => integrable_finset_sum _ (fun j hj => (hM i hi j hj).norm))
  calc (∫ q : Plane, ‖∑ i ∈ s, ∑ j ∈ s, (c i*conj (c j))*M i j q‖)
      ≤ ∫ q : Plane, ∑ i ∈ s, ∑ j ∈ s, ‖M i j q‖ := by
        apply integral_mono hint.norm hg
        intro q
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
        rw [norm_mul,norm_mul,RCLike.norm_conj]
        have h1 : ‖c i‖*‖c j‖≤1 := by
          nlinarith [norm_nonneg (c i),norm_nonneg (c j),hc i,hc j]
        exact mul_le_of_le_one_left (norm_nonneg _) h1
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ q : Plane, ‖M i j q‖ := by
        rw [integral_finset_sum _ (fun i hi => integrable_finset_sum _
          (fun j hj => (hM i hi j hj).norm))]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        exact integral_finset_sum _ (fun j hj => (hM i hi j hj).norm)

end Mass

/-! ### The actual finite-ball chain -/

section Actual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem solution_comb (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A B : Index →₀ ℂ) (z : ℂ) (a : ℝ)
    (ha : 0<a) (ha1 : a≤1) :
    RestrictedTEFiniteBalls.solution p ρ χ R b hρ hχ hi (fun a => (a : ℂ)⁻¹ • (A+z • B)) a=
      RestrictedTEFiniteBalls.solution p ρ χ R b hρ hχ hi (fun a => (a : ℂ)⁻¹ • A) a+
        z • RestrictedTEFiniteBalls.solution p ρ χ R b hρ hχ hi (fun a => (a : ℂ)⁻¹ • B) a := by
  have hd : 0<a ∧ a≤1 := ⟨ha,ha1⟩
  unfold RestrictedTEFiniteBalls.solution
  have hs : (a : ℂ)⁻¹ • (A+z • B)=(a : ℂ)⁻¹ • A+z • ((a : ℂ)⁻¹ • B) := by
    rw [smul_add,smul_comm]
  simp only [dif_pos hd,← OQ14.RestrictedTEDatumLinear.solutionMap_apply]
  rw [hs,map_add,map_smul _ z]

omit [DecidableEq ι] in
theorem source_ae (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A B : Index →₀ ℂ) (z : ℂ) (a : ℝ)
    (ha : 0<a) (ha1 : a≤1) (j : Fin 3) :
    RestrictedTESourceMass.source p ρ χ R b hρ hχ hi (A+z • B) a j =ᵐ[volume]
      (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a+
        z • RestrictedTESourceMass.source p ρ χ R b hρ hχ hi B a) j := by
  unfold RestrictedTESourceMass.source
  rw [solution_comb p ρ χ R b hρ hχ hi A B z a ha ha1]
  have h1 := OQ14.MaterialSourceLinear.add (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
    (RestrictedTEFiniteBalls.solution p ρ χ R b hρ hχ hi (fun a => (a : ℂ)⁻¹ • A) a)
    (z • RestrictedTEFiniteBalls.solution p ρ χ R b hρ hχ hi (fun a => (a : ℂ)⁻¹ • B) a) j
  have h2 := OQ14.MaterialSourceLinear.smul (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ) z
    (RestrictedTEFiniteBalls.solution p ρ χ R b hρ hχ hi (fun a => (a : ℂ)⁻¹ • B) a) j
  filter_upwards [h1,h2] with y hy1 hy2
  rw [hy1,hy2]
  rfl

theorem electric_comb (A B : Index →₀ ℂ) (z : ℂ) (a : ℝ) :
    electric ((a : ℂ)⁻¹ • (A+z • B))=electric ((a : ℂ)⁻¹ • A)+z • electric ((a : ℂ)⁻¹ • B) := by
  have hs : (a : ℂ)⁻¹ • (A+z • B)=(a : ℂ)⁻¹ • A+z • ((a : ℂ)⁻¹ • B) := by
    rw [smul_add,smul_comm]
  rw [hs,OQ14.RestrictedTEFieldLinear.electric_add,RestrictedTEScale.electric_smul z ((a : ℂ)⁻¹ • B)]

theorem magnetic_comb (A B : Index →₀ ℂ) (z : ℂ) (a : ℝ) :
    magnetic ((a : ℂ)⁻¹ • (A+z • B))=magnetic ((a : ℂ)⁻¹ • A)+z • magnetic ((a : ℂ)⁻¹ • B) := by
  have hs : (a : ℂ)⁻¹ • (A+z • B)=(a : ℂ)⁻¹ • A+z • ((a : ℂ)⁻¹ • B) := by
    rw [smul_add,smul_comm]
  rw [hs,OQ14.RestrictedTEFieldLinear.magnetic_add,RestrictedTEScale.magnetic_smul z ((a : ℂ)⁻¹ • B)]

/-- The actual complete parity total electric field of the finite-ball inverse, at a plane point. -/
def totalE (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (a : ℝ) (A : Index →₀ ℂ) (q : Plane) : Vector :=
  ParityPlaneFields.totalElectric 1 (b/a) (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a)
    (electric ((a : ℂ)⁻¹ • A)) (MaxwellPlaneTail.planePoint q)

/-- The actual complete parity total magnetic field of the finite-ball inverse, at a plane point. -/
def totalH (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (a : ℝ) (A : Index →₀ ℂ) (q : Plane) : Vector :=
  ParityPlaneFields.totalMagnetic 1 (b/a) (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a)
    (magnetic ((a : ℂ)⁻¹ • A)) (MaxwellPlaneTail.planePoint q)

theorem totalE_comb (p : ℝ → ι → Space) (ρ χ R b d a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (hd : 0<d) (ha : 0<a) (ha1 : a≤1)
    (hh : ∀ l, d+ρ*a≤|p a l 2|) (A B : Index →₀ ℂ) (z : ℂ) (q : Plane) :
    totalE p ρ χ R b hρ hχ hi a (A+z • B) q=
      totalE p ρ χ R b hρ hχ hi a A q+z • totalE p ρ χ R b hρ hχ hi a B q := by
  have hA : Admissible R d (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a) :=
    RestrictedTEFiniteBalls.source_admissible p ρ χ R b d a hρ hχ hi
    (fun a => (a : ℂ)⁻¹ • A) ha ha1 hh
  have hB : Admissible R d (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi B a) :=
    RestrictedTEFiniteBalls.source_admissible p ρ χ R b d a hρ hχ hi
    (fun a => (a : ℂ)⁻¹ • B) ha ha1 hh
  unfold totalE
  rw [total_electric_congr 1 (b/a) _ _ (source_ae p ρ χ R b hρ hχ hi A B z a ha ha1) _ _,
    electric_comb,total_electric_comb 1 (b/a) R d hd _ _ hA hB z _ _ q]

theorem totalH_comb (p : ℝ → ι → Space) (ρ χ R b d a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (hd : 0<d) (ha : 0<a) (ha1 : a≤1)
    (hh : ∀ l, d+ρ*a≤|p a l 2|) (A B : Index →₀ ℂ) (z : ℂ) (q : Plane) :
    totalH p ρ χ R b hρ hχ hi a (A+z • B) q=
      totalH p ρ χ R b hρ hχ hi a A q+z • totalH p ρ χ R b hρ hχ hi a B q := by
  have hA : Admissible R d (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a) :=
    RestrictedTEFiniteBalls.source_admissible p ρ χ R b d a hρ hχ hi
    (fun a => (a : ℂ)⁻¹ • A) ha ha1 hh
  have hB : Admissible R d (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi B a) :=
    RestrictedTEFiniteBalls.source_admissible p ρ χ R b d a hρ hχ hi
    (fun a => (a : ℂ)⁻¹ • B) ha ha1 hh
  unfold totalH
  rw [total_magnetic_congr 1 (b/a) _ _ (source_ae p ρ χ R b hρ hχ hi A B z a ha ha1) _ _,
    magnetic_comb,total_magnetic_comb 1 (b/a) R d hd _ _ hA hB z _ _ q]

/-- The actual total electric field at a plane point as a `ℂ`-linear map of the coefficient vector. -/
def totalEMap (p : ℝ → ι → Space) (ρ χ R b d a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (hd : 0<d) (ha : 0<a) (ha1 : a≤1)
    (hh : ∀ l, d+ρ*a≤|p a l 2|) (q : Plane) : (Index →₀ ℂ) →ₗ[ℂ] Vector :=
  linearOfComb (fun A => totalE p ρ χ R b hρ hχ hi a A q)
    (fun A B z => totalE_comb p ρ χ R b d a hρ hχ hi hd ha ha1 hh A B z q)

def totalHMap (p : ℝ → ι → Space) (ρ χ R b d a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (hd : 0<d) (ha : 0<a) (ha1 : a≤1)
    (hh : ∀ l, d+ρ*a≤|p a l 2|) (q : Plane) : (Index →₀ ℂ) →ₗ[ℂ] Vector :=
  linearOfComb (fun A => totalH p ρ χ R b hρ hχ hi a A q)
    (fun A B z => totalH_comb p ρ χ R b d a hρ hχ hi hd ha ha1 hh A B z q)

/-- The sesquilinear polarization form of the actual complete flux density at a plane point. -/
def fluxForm (p : ℝ → ι → Space) (ρ χ R b a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (q : Plane) (A A' : Index →₀ ℂ) : ℂ :=
  crossProduct (totalE p ρ χ R b hρ hχ hi a A q) (conjugate (totalH p ρ χ R b hρ hχ hi a A' q)) 2

theorem fluxForm_sesq (p : ℝ → ι → Space) (ρ χ R b d a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (hd : 0<d) (ha : 0<a) (ha1 : a≤1)
    (hh : ∀ l, d+ρ*a≤|p a l 2|) (q : Plane) :
    OQ14.RestrictedTEPolarization.Sesq (fluxForm p ρ χ R b a hρ hχ hi q) :=
  flux_sesq (totalEMap p ρ χ R b d a hρ hχ hi hd ha ha1 hh q)
    (totalHMap p ρ χ R b d a hρ hχ hi hd ha ha1 hh q)

omit [DecidableEq ι] in
/-- The literal complete flux density of the actual inverse is the diagonal of the sesquilinear form. -/
theorem totalFlux_eq_diagonal (p : ℝ → ι → Space) (ρ χ R b a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (q : Plane) (A : Index →₀ ℂ) :
    RestrictedTETotalFlux.totalFlux (b/a) (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a)
      ((a : ℂ)⁻¹ • A) q=fluxForm p ρ χ R b a hρ hχ hi q A A := rfl

/-! ### The exact finite-dipole side -/

/-- Exact finite-dipole electric field of the actual polarizations at a plane point. -/
def dipE (p : ℝ → ι → Space) (ρ χ a : ℝ) (A : Index →₀ ℂ) (q : Plane) : Vector :=
  FinitePlaneDipole.dipoles (p a) (fun _ => ρ*a)
    (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A) (p a l)))
    (MaxwellPlaneTail.planePoint q)

/-- The incident magnetic field of the scaled input at a plane point. -/
def incH (a : ℝ) (A : Index →₀ ℂ) (q : Plane) : Vector :=
  magnetic ((a : ℂ)⁻¹ • A) (MaxwellPlaneTail.planePoint q)

theorem polarization_comb (χ : ℝ) (u v : Vector) (z : ℂ) (j : Fin 3) :
    StaticSpherePolarization.polarization χ (u+z • v) j=
      StaticSpherePolarization.polarization χ u j+z*StaticSpherePolarization.polarization χ v j := by
  simp only [StaticSpherePolarization.polarization,Pi.add_apply,Pi.smul_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

omit [DecidableEq ι] in
theorem dipE_comb (p : ℝ → ι → Space) (ρ χ a : ℝ) (A B : Index →₀ ℂ) (z : ℂ) (q : Plane) :
    dipE p ρ χ a (A+z • B) q=dipE p ρ χ a A q+z • dipE p ρ χ a B q := by
  funext i
  have hE (l : ι) (j : Fin 3) := polarization_comb χ (electric ((a : ℂ)⁻¹ • A) (p a l))
    (electric ((a : ℂ)⁻¹ • B) (p a l)) z j
  simp only [dipE,FinitePlaneDipole.dipoles,StaticBallPlaneDipole.dipole,electric_comb,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul,Finset.mul_sum,← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hE l j]
  ring

theorem incH_comb (a : ℝ) (A B : Index →₀ ℂ) (z : ℂ) (q : Plane) :
    incH a (A+z • B) q=incH a A q+z • incH a B q := by
  simp only [incH,magnetic_comb]
  rfl

/-- The sesquilinear form of the exact finite-dipole flux density at a plane point. -/
def dipForm (p : ℝ → ι → Space) (ρ χ a : ℝ) (q : Plane) (A A' : Index →₀ ℂ) : ℂ :=
  crossProduct (dipE p ρ χ a A q) (conjugate (incH a A' q)) 2

theorem dipForm_sesq (p : ℝ → ι → Space) (ρ χ a : ℝ) (q : Plane) :
    OQ14.RestrictedTEPolarization.Sesq (dipForm p ρ χ a q) :=
  flux_sesq (linearOfComb (fun A => dipE p ρ χ a A q) (fun A B z => dipE_comb p ρ χ a A B z q))
    (linearOfComb (fun A => incH a A q) (fun A B z => incH_comb a A B z q))

omit [DecidableEq ι] in
theorem dipoleFlux_eq_diagonal (p : ℝ → ι → Space) (ρ χ a : ℝ) (q : Plane) (A : Index →₀ ℂ) :
    RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
      (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A) (p a l)))
      ((a : ℂ)⁻¹ • A) q=dipForm p ρ χ a q A A := rfl

/-! ### Uniform finite-input convergence by polarization -/

open Filter
open scoped Topology ComplexConjugate

/-- The difference of the actual complete flux form and the exact finite-dipole flux form. -/
def diffForm (p : ℝ → ι → Space) (ρ χ R b a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (q : Plane) (A A' : Index →₀ ℂ) : ℂ :=
  fluxForm p ρ χ R b a hρ hχ hi q A A'-dipForm p ρ χ a q A A'

theorem diffForm_sesq (p : ℝ → ι → Space) (ρ χ R b d a : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (hd : 0<d) (ha : 0<a) (ha1 : a≤1)
    (hh : ∀ l, d+ρ*a≤|p a l 2|) (q : Plane) :
    OQ14.RestrictedTEPolarization.Sesq (diffForm p ρ χ R b a hρ hχ hi q) :=
  sesq_sub (fluxForm_sesq p ρ χ R b d a hρ hχ hi hd ha ha1 hh q) (dipForm_sesq p ρ χ a q)

theorem eventually_integrable (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (A : Index →₀ ℂ) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, Integrable (fun q : Plane => diffForm p ρ χ R b a hρ hχ hi q A A) := by
  obtain ⟨C,hC,η,hη,hest⟩ := RestrictedTEAsymptotics.eventual_estimates p ρ χ δ R b hρ hχ hδ hb hsep hi A
  obtain ⟨B,hB,hprofile⟩ := RestrictedTEDipoleError.from_estimates (ι := ι) A
  let S := RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A
  let P := fun (a : ℝ) l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A) (p a l))
  have hp : ∀ᶠ a : ℝ in 𝓝[>] 0,
      Integrable (fun q : Plane => staticMixed (S a) ((a : ℂ)⁻¹ • A) q-
        RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q) ∧
      Admissible R (γ*a) (S a) := by
    have hn : ∀ᶠ a : ℝ in 𝓝[>] 0, a<η := nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hn,self_mem_nhdsWithin] with a had ha
    change 0<a at ha
    obtain ⟨ha1,he⟩ := hest a ha had
    have hprof := hprofile (p a) ρ a χ δ R 1 b C C γ hρ ha hχ hγ (hh a ha ha1)
      (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1)
      (RestrictedTEAsymptotics.forcing p ρ χ R hρ hχ hi A a)
      (fun l => electric ((a : ℂ)⁻¹ • A) (p a l)) he
    dsimp only at hprof
    rw [← RestrictedTESourceMass.source_actual p ρ χ R b hρ hχ hi A a ha ha1] at hprof
    have hs : Admissible R (γ*a) (S a) := RestrictedTEFiniteBalls.source_admissible p ρ χ R b (γ*a) a hρ hχ hi
      (fun a => (a : ℂ)⁻¹ • A) ha ha1 (fun l => by simpa only [add_mul] using hh a ha ha1 l)
    exact ⟨hprof.1,hs⟩
  let T := max 2 (2*R)
  have hT : 2≤T := le_max_left _ _
  have hTR : 2*R≤T := le_max_right _ _
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a≤T+R := by
    have hl := (show Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul γ
    simp only [mul_zero] at hl
    exact (hl.eventually (gt_mem_nhds (by linarith : 0<T+R))).mono (fun _ h => h.le)
  obtain ⟨Ci,Cp,hCi,hCp,hwhole⟩ := RestrictedTETotalFlux.whole_bounds A R hR
  filter_upwards [hp,hsmall,self_mem_nhdsWithin] with a hp hdM ha
  change 0<a at ha
  have hd := mul_pos hγ ha
  have htotal := (hwhole (b/a) T (γ*a) hd hT hTR hdM (S a) hp.2 (a : ℂ)⁻¹).2.1
  obtain ⟨_,_,hs⟩ := RestrictedTEStaticFlux.static_mass ((a : ℂ)⁻¹ • A)
  have hstatic := (hs R (γ*a) hd (S a) hp.2).1
  refine ((htotal.sub hstatic).add hp.1).congr (Filter.Eventually.of_forall (fun q => ?_))
  simp only [Pi.add_apply,Pi.sub_apply]
  change _=RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
    RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q
  ring

theorem uniform_form (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (s : Finset Index) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A : Index →₀ ℂ, (∀ i, i∉s → A i=0) → (∀ i, ‖A i‖≤1) →
      Integrable (fun q : Plane => diffForm p ρ χ R b a hρ hχ hi q A A) ∧
        (∫ q : Plane, ‖diffForm p ρ χ R b a hρ hχ hi q A A‖)≤ε := by
  -- masses of the fixed-input differences
  have hmass (w : Index →₀ ℂ) : Tendsto (fun a : ℝ => ∫ q : Plane, ‖diffForm p ρ χ R b a hρ hχ hi q w w‖)
      (𝓝[>] 0) (𝓝 0) :=
    RestrictedTEDipoleLimit.actual_inverse_to_dipoles p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh w
  have hint (w : Index →₀ ℂ) := eventually_integrable p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh w
  let e : Index → (Index →₀ ℂ) := fun i => Finsupp.single i 1
  let m : (Index →₀ ℂ) → ℝ → ℝ := fun w a => ∫ q : Plane, ‖diffForm p ρ χ R b a hρ hχ hi q w w‖
  let U : Index → Index → ℝ → ℝ := fun i j a =>
    (1/4)*(m (e i+e j) a+m (e i-e j) a+m (e i+I • e j) a+m (e i-I • e j) a)
  have hU (i j : Index) : Tendsto (U i j) (𝓝[>] 0) (𝓝 0) := by
    have := ((((hmass (e i+e j)).add (hmass (e i-e j))).add (hmass (e i+I • e j))).add
      (hmass (e i-I • e j))).const_mul (1/4 : ℝ)
    rw [show (1/4 : ℝ)*(0+0+0+0)=0 by norm_num] at this
    exact this
  have hlt1 : ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 := nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
  have hentry (i j : Index) : ∀ᶠ a : ℝ in 𝓝[>] 0,
      Integrable (fun q : Plane => diffForm p ρ χ R b a hρ hχ hi q (e i) (e j)) ∧
        (∫ q : Plane, ‖diffForm p ρ χ R b a hρ hχ hi q (e i) (e j)‖)≤U i j a := by
    filter_upwards [hint (e i+e j),hint (e i-e j),hint (e i+I • e j),hint (e i-I • e j),
      self_mem_nhdsWithin,hlt1] with a h1 h2 h3 h4 ha ha1
    change 0<a at ha
    have hsq := fun q => diffForm_sesq p ρ χ R b (γ*a) a hρ hχ hi (mul_pos hγ ha) ha ha1.le
      (fun l => by simpa only [add_mul] using hh a ha ha1.le l) q
    have hq (q : Plane) : diffForm p ρ χ R b a hρ hχ hi q (e i) (e j)=
        (1/4 : ℂ)*((diffForm p ρ χ R b a hρ hχ hi q (e i+e j) (e i+e j)-
          diffForm p ρ χ R b a hρ hχ hi q (e i-e j) (e i-e j))+
          I*(diffForm p ρ χ R b a hρ hχ hi q (e i+I • e j) (e i+I • e j)-
          diffForm p ρ χ R b a hρ hχ hi q (e i-I • e j) (e i-I • e j))) := by
      have := (hsq q).polarization (e i) (e j)
      simpa only [smul_eq_mul] using this
    simp only [hq]
    exact entry_bound _ _ _ _ h1 h2 h3 h4
  have hall : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ i ∈ s, ∀ j ∈ s,
      Integrable (fun q : Plane => diffForm p ρ χ R b a hρ hχ hi q (e i) (e j)) ∧
        (∫ q : Plane, ‖diffForm p ρ χ R b a hρ hχ hi q (e i) (e j)‖)≤U i j a := by
    rw [Filter.eventually_all_finset]
    intro i hi'
    rw [Filter.eventually_all_finset]
    intro j hj'
    exact hentry i j
  have hsum : ∀ᶠ a : ℝ in 𝓝[>] 0, (∑ i ∈ s, ∑ j ∈ s, U i j a)<ε := by
    have ht : Tendsto (fun a : ℝ => ∑ i ∈ s, ∑ j ∈ s, U i j a) (𝓝[>] 0) (𝓝 0) := by
      have := tendsto_finset_sum s (fun i _ => tendsto_finset_sum s (fun j _ => hU i j))
      simpa using this
    exact ht.eventually (gt_mem_nhds hε)
  filter_upwards [hall,hsum,self_mem_nhdsWithin,hlt1] with a hall hsum ha ha1
  change 0<a at ha
  intro A hA hA1
  have hsq := fun q => diffForm_sesq p ρ χ R b (γ*a) a hρ hχ hi (mul_pos hγ ha) ha ha1.le
    (fun l => by simpa only [add_mul] using hh a ha ha1.le l) q
  have hAeq : A=∑ i ∈ s, A i • e i := by
    ext k
    classical
    simp only [e,Finsupp.coe_finset_sum,Finset.sum_apply,Finsupp.smul_apply,smul_eq_mul]
    by_cases hk : k ∈ s
    · simp [Finsupp.single_apply,hk]
    · simp [Finsupp.single_apply,hk,hA k hk]
  have hexp (q : Plane) : diffForm p ρ χ R b a hρ hχ hi q A A=
      ∑ i ∈ s, ∑ j ∈ s, (A i*conj (A j))*diffForm p ρ χ R b a hρ hχ hi q (e i) (e j) := by
    have h := sesq_expand (hsq q) s e (fun i => A i) (fun j => A j)
    simp only [smul_eq_mul] at h
    rw [← hAeq] at h
    exact h
  obtain ⟨hI,hB⟩ := double_sum_bound s (fun i j q => diffForm p ρ χ R b a hρ hχ hi q (e i) (e j))
    (fun i hi j hj => (hall i hi j hj).1) A hA1
  simp only [hexp]
  refine ⟨hI,hB.trans ?_⟩
  exact (Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => (hall i hi j hj).2))).trans hsum.le

/-- Uniform finite-input whole-plane L1 convergence of the actual complete parity flux to the exact finite-dipole
flux: for every finite set `s` of harmonic indices and every `ε>0`, for all sufficiently small `a>0` and
simultaneously for every coefficient vector supported in `s` with all entries of modulus at most one,
the flux difference is integrable with whole-plane L1 mass at most `ε`. -/
theorem uniform_actual_inverse_to_dipoles (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (s : Finset Index) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ A : Index →₀ ℂ, (∀ i, i∉s → A i=0) → (∀ i, ‖A i‖≤1) →
      Integrable (fun q : Plane =>
        RestrictedTETotalFlux.totalFlux (b/a) (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a)
            ((a : ℂ)⁻¹ • A) q-
          RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
            (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A) (p a l)))
            ((a : ℂ)⁻¹ • A) q) ∧
      (∫ q : Plane, ‖RestrictedTETotalFlux.totalFlux (b/a)
            (RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A a) ((a : ℂ)⁻¹ • A) q-
          RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a)
            (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A) (p a l)))
            ((a : ℂ)⁻¹ • A) q‖)≤ε :=
  (uniform_form p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh s ε hε).mono
    (fun _ h A hA hA1 => h A hA hA1)

end Actual

end OQ14.RestrictedTETotalLinear
#print axioms OQ14.RestrictedTETotalLinear.admissible_comb
#print axioms OQ14.RestrictedTETotalLinear.total_electric_congr
#print axioms OQ14.RestrictedTETotalLinear.total_magnetic_congr
#print axioms OQ14.RestrictedTETotalLinear.total_electric_comb
#print axioms OQ14.RestrictedTETotalLinear.total_magnetic_comb
#print axioms OQ14.RestrictedTETotalLinear.flux_sesq
#print axioms OQ14.RestrictedTETotalLinear.solution_comb
#print axioms OQ14.RestrictedTETotalLinear.source_ae
#print axioms OQ14.RestrictedTETotalLinear.totalE_comb
#print axioms OQ14.RestrictedTETotalLinear.totalH_comb
#print axioms OQ14.RestrictedTETotalLinear.fluxForm_sesq
#print axioms OQ14.RestrictedTETotalLinear.totalFlux_eq_diagonal
#print axioms OQ14.RestrictedTETotalLinear.dipE_comb
#print axioms OQ14.RestrictedTETotalLinear.dipForm_sesq
#print axioms OQ14.RestrictedTETotalLinear.dipoleFlux_eq_diagonal
#print axioms OQ14.RestrictedTETotalLinear.entry_bound
#print axioms OQ14.RestrictedTETotalLinear.double_sum_bound
#print axioms OQ14.RestrictedTETotalLinear.sesq_expand
#print axioms OQ14.RestrictedTETotalLinear.sesq_sub
#print axioms OQ14.RestrictedTETotalLinear.eventually_integrable
#print axioms OQ14.RestrictedTETotalLinear.uniform_form
#print axioms OQ14.RestrictedTETotalLinear.uniform_actual_inverse_to_dipoles
#print axioms OQ14.RestrictedTETotalLinear.source_comb_apply
#print axioms OQ14.RestrictedTETotalLinear.response_congr
#print axioms OQ14.RestrictedTETotalLinear.ext_electric_congr
#print axioms OQ14.RestrictedTETotalLinear.ext_magnetic_congr
#print axioms OQ14.RestrictedTETotalLinear.parity_electric_congr
#print axioms OQ14.RestrictedTETotalLinear.parity_magnetic_congr
#print axioms OQ14.RestrictedTETotalLinear.response_comb
#print axioms OQ14.RestrictedTETotalLinear.ext_electric_comb
#print axioms OQ14.RestrictedTETotalLinear.ext_magnetic_comb
#print axioms OQ14.RestrictedTETotalLinear.parity_electric_comb
#print axioms OQ14.RestrictedTETotalLinear.parity_magnetic_comb
#print axioms OQ14.RestrictedTETotalLinear.linearOfComb_apply
#print axioms OQ14.RestrictedTETotalLinear.cross_two
#print axioms OQ14.RestrictedTETotalLinear.sesq_zero_left
#print axioms OQ14.RestrictedTETotalLinear.sesq_zero_right
#print axioms OQ14.RestrictedTETotalLinear.sesq_sum_left
#print axioms OQ14.RestrictedTETotalLinear.sesq_sum_right
#print axioms OQ14.RestrictedTETotalLinear.electric_comb
#print axioms OQ14.RestrictedTETotalLinear.magnetic_comb
#print axioms OQ14.RestrictedTETotalLinear.polarization_comb
#print axioms OQ14.RestrictedTETotalLinear.incH_comb
#print axioms OQ14.RestrictedTETotalLinear.diffForm_sesq
