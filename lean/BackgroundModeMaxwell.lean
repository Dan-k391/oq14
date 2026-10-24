import BackgroundCoreTransmission
import SourceGlobalCorrection
import SourceCorrectionLocalBounds
import SourceExteriorSmooth
import TestFieldLocalization

/-! Weak Maxwell structure of the layered background mode.  Complex conjugation of weak forced
Maxwell pairs, linear combinations of forced pairs, and the background fields built from the
actual source-mode fields of a layered stack. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BackgroundModeMaxwell
open MeasureTheory Filter OQ14.Maxwell OQ14.MaterialMaxwell OQ14.MagneticResponse
  OQ14.DynamicSource OQ14.ForcedMaxwellResponse
open scoped ComplexConjugate Topology

/-! ### Conjugation of weak forced Maxwell pairs -/

/-- Componentwise conjugate of a field. -/
def conjField (E : Field) : Field := fun x i => conj (E x i)

/-- Minus the componentwise conjugate of a field. -/
def negConjField (H : Field) : Field := fun x i => -conj (H x i)

theorem dcoord_conj (f : Space → ℂ) (x : Space) (i : Fin 3) :
    dcoord (fun y => conj (f y)) x i=conj (dcoord f x i) := by
  have h : (fun y => conj (f y))=(Complex.conjCLE : ℂ → ℂ) ∘ f := by
    funext y
    simp
  unfold dcoord
  rw [h,ContinuousLinearEquiv.comp_fderiv]
  simp

theorem dcoord_real (g : Space → ℂ) (hg : ∀ y, conj (g y)=g y) (x : Space) (i : Fin 3) :
    conj (dcoord g x i)=dcoord g x i := by
  rw [← dcoord_conj]
  congr 1
  funext y
  exact hg y

theorem conj_contDiff (f : Test) : ContDiff ℝ (⊤ : ℕ∞) (fun x => conj (f.val x)) :=
  Complex.conjCLE.contDiff.comp (f.val.smooth (⊤ : ℕ∞))

theorem conj_compact (f : Test) : HasCompactSupport (fun x => conj (f.val x)) :=
  f.property.comp_left (g := fun z : ℂ => conj z) (map_zero _)

/-- Conjugation of a compactly supported Schwartz test function. -/
def conjTest (f : Test) : Test :=
  ⟨FourierL2.compactSmoothSchwartz (fun x => conj (f.val x)) (conj_contDiff f) (conj_compact f),
    conj_compact f⟩

theorem conjTest_apply (f : Test) (x : Space) : (conjTest f).val x=conj (f.val x) := rfl

theorem testPartial_conjTest (i : Fin 3) (f : Test) :
    testPartial i (conjTest f)=conjTest (testPartial i f) := by
  apply Subtype.ext
  ext x
  change dcoord (fun y => conj (f.val y)) x i=conj (dcoord (f.val : Space → ℂ) x i)
  exact dcoord_conj _ x i

theorem fieldPair_conj (E : Field) (i : Fin 3) (f : Test) :
    fieldPair (conjField E) i f=conj (fieldPair E i (conjTest f)) := by
  unfold fieldPair
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp [conjField,conjTest_apply]

theorem fieldPair_negConj (H : Field) (i : Fin 3) (f : Test) :
    fieldPair (negConjField H) i f=-conj (fieldPair H i (conjTest f)) := by
  unfold fieldPair
  rw [← integral_conj,← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  simp [negConjField,conjTest_apply]

theorem curlPair_conj (E : Field) (i : Fin 3) (f : Test) :
    curlPair (fieldPair (conjField E)) i f=conj (curlPair (fieldPair E) i (conjTest f)) := by
  unfold curlPair
  rw [fieldPair_conj,fieldPair_conj,testPartial_conjTest,testPartial_conjTest,map_sub]

theorem curlPair_negConj (H : Field) (i : Fin 3) (f : Test) :
    curlPair (fieldPair (negConjField H)) i f=-conj (curlPair (fieldPair H) i (conjTest f)) := by
  unfold curlPair
  rw [fieldPair_negConj,fieldPair_negConj,testPartial_conjTest,testPartial_conjTest,map_sub]
  ring

theorem integral_conj_pair (ρ : Space → ℂ) (f : Test) :
    (∫ x,conj (ρ x)*f.val x)=conj (∫ x,ρ x*(conjTest f).val x) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp [conjTest_apply]

/-- **Conjugation.** If `(E,H)` is a weak forced pair for the real wavenumber `k`, then `(conj E, -conj H)`
is a weak forced pair for `conj ρ`. -/
theorem testForced_conj (k : ℝ) (ρ : Fin 3 → Space → ℂ) (E H : Field) (h : TestForced k ρ E H) :
    TestForced k (fun i x => conj (ρ i x)) (conjField E) (negConjField H) := by
  intro i f
  obtain ⟨h1,h2⟩ := h i (conjTest f)
  have hk : conj (k : ℂ)=(k : ℂ) := Complex.conj_ofReal k
  constructor
  · rw [curlPair_conj,h1,fieldPair_negConj,map_mul,map_mul,hk,Complex.conj_I]
    ring
  · rw [curlPair_negConj,h2,fieldPair_conj,integral_conj_pair,map_mul,map_neg,map_mul,hk,
      Complex.conj_I,map_add]
    ring

/-! ### Linear combinations of forced pairs -/

theorem fieldPair_add (E F : Field) (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (i : Fin 3) (f : Test) :
    fieldPair (E+F) i f=fieldPair E i f+fieldPair F i f := by
  unfold fieldPair
  simp only [Pi.add_apply,add_mul]
  exact integral_add (PointSingularity.test_product_integrable _ _ (hE i) f.val.continuous f.property)
    (PointSingularity.test_product_integrable _ _ (hF i) f.val.continuous f.property)

theorem curlPair_add (E F : Field) (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (i : Fin 3) (f : Test) :
    curlPair (fieldPair (E+F)) i f=curlPair (fieldPair E) i f+curlPair (fieldPair F) i f := by
  unfold curlPair
  rw [fieldPair_add E F hE hF,fieldPair_add E F hE hF]
  ring

theorem locallyIntegrable_smul (c : ℂ) (E : Field) (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (i : Fin 3) : LocallyIntegrable (fun x => (c • E) x i) := by
  simpa only [Pi.smul_apply,smul_eq_mul] using (hE i).smul c

theorem locallyIntegrable_add (E F : Field) (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (i : Fin 3) :
    LocallyIntegrable (fun x => (E+F) x i) := by
  simpa only [Pi.add_apply] using (hE i).add (hF i)

theorem locallyIntegrable_conj (E : Field) (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (i : Fin 3) :
    LocallyIntegrable (fun x => conjField E x i) := by
  refine (hE i).mono (Complex.continuous_conj.comp_aestronglyMeasurable (hE i).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun x => by simp [conjField])

theorem locallyIntegrable_negConj (E : Field) (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (i : Fin 3) :
    LocallyIntegrable (fun x => negConjField E x i) := by
  refine (hE i).mono ((Complex.continuous_conj.comp_aestronglyMeasurable (hE i).aestronglyMeasurable).neg) ?_
  exact Filter.Eventually.of_forall (fun x => by simp [negConjField])

theorem testForced_add (k : ℝ) (ρ ρ' : Fin 3 → Space → ℂ) (E H E' H' : Field)
    (hρ : ∀ i, LocallyIntegrable (ρ i)) (hρ' : ∀ i, LocallyIntegrable (ρ' i))
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hE' : ∀ i, LocallyIntegrable (fun x => E' x i)) (hH' : ∀ i, LocallyIntegrable (fun x => H' x i))
    (h : TestForced k ρ E H) (h' : TestForced k ρ' E' H') :
    TestForced k (fun i x => ρ i x+ρ' i x) (E+E') (H+H') := by
  intro i f
  obtain ⟨a1,a2⟩ := h i f
  obtain ⟨b1,b2⟩ := h' i f
  have hi : (∫ x,(ρ i x+ρ' i x)*f.val x)=(∫ x,ρ i x*f.val x)+∫ x,ρ' i x*f.val x := by
    simp only [add_mul]
    exact integral_add (PointSingularity.test_product_integrable _ _ (hρ i) f.val.continuous f.property)
      (PointSingularity.test_product_integrable _ _ (hρ' i) f.val.continuous f.property)
  constructor
  · rw [curlPair_add E E' hE hE',a1,b1,fieldPair_add H H' hH hH']
    ring
  · rw [curlPair_add H H' hH hH',a2,b2,fieldPair_add E E' hE hE',hi]
    ring

theorem testForced_smul (k : ℝ) (c : ℂ) (ρ : Fin 3 → Space → ℂ) (E H : Field) (h : TestForced k ρ E H) :
    TestForced k (fun i x => c*ρ i x) (c • E) (c • H) := by
  intro i f
  obtain ⟨a1,a2⟩ := h i f
  have hi : (∫ x,(c*ρ i x)*f.val x)=c*∫ x,ρ i x*f.val x := by
    simp only [mul_assoc]
    exact integral_const_mul c _
  constructor
  · rw [TestFieldLocalization.curlPair_smul,a1,TestFieldLocalization.fieldPair_smul]
    ring
  · rw [TestFieldLocalization.curlPair_smul,a2,TestFieldLocalization.fieldPair_smul,hi]
    ring


/-! ### The source-mode formulas as functions of a radial state, for real polynomials -/

section Formulas
open OQ14.HarmonicPolynomial OQ14.SourceRadialSystem OQ14.SourceCoreReaction OQ14.HankelRealBasis
  OQ14.ModalAlgebra

/-- The electric formula of a TM mode applied to a radial state `(u,p)` with inverse permittivity `s`. -/
def Eform (l : ℕ) (P : Poly) (s u p : ℂ) (x : Space) (i : Fin 3) : ℂ :=
  (p/(‖x‖ : ℂ)^l)*dcoord (complexEvaluate P) x i+
    (s*((l : ℂ)*(l+1)*u/(‖x‖ : ℂ)^(l+3))-(l : ℂ)*p/(‖x‖ : ℂ)^(l+2))*(x i : ℂ)*complexEvaluate P x

/-- The magnetic formula of a TM mode applied to a radial state with first component `u`. -/
def Hform (l : ℕ) (P : Poly) (u : ℂ) (x : Space) (i : Fin 3) : ℂ :=
  -Complex.I*(u/(‖x‖ : ℂ)^(l+1))*DebyeRadialTrace.angularToroidal P x i

theorem electric_eq_Eform (d : Data) (P : Poly) (x : Space) (i : Fin 3) :
    SourceUnclippedMaxwell.electric d P x i=
      Eform d.l P (inverseSigma d ‖x‖) (raw d ‖x‖).1 (raw d ‖x‖).2 x i := rfl

theorem magnetic_eq_Hform (d : Data) (P : Poly) (x : Space) (i : Fin 3) :
    SourceUnclippedMaxwell.magnetic d P x i=Hform d.l P (raw d ‖x‖).1 x i := rfl

theorem conj_cE (P : Poly) (x : Space) : conj (complexEvaluate P x)=complexEvaluate P x := by
  simp [complexEvaluate]

theorem conj_dcoord_cE (P : Poly) (x : Space) (i : Fin 3) :
    conj (dcoord (complexEvaluate P) x i)=dcoord (complexEvaluate P) x i :=
  dcoord_real _ (fun y => conj_cE P y) x i

theorem conj_angularToroidal (P : Poly) (x : Space) (i : Fin 3) :
    conj (DebyeRadialTrace.angularToroidal P x i)=DebyeRadialTrace.angularToroidal P x i := by
  fin_cases i <;>
  simp [DebyeRadialTrace.angularToroidal,map_sub,map_mul,conj_dcoord_cE]

theorem conj_Eform (l : ℕ) (P : Poly) (s u p : ℂ) (x : Space) (i : Fin 3) :
    conj (Eform l P s u p x i)=Eform l P (conj s) (conj u) (conj p) x i := by
  unfold Eform
  simp only [map_add,map_mul,map_div₀,map_sub,map_pow,map_natCast,map_one,Complex.conj_ofReal,
    conj_cE,conj_dcoord_cE]

theorem conj_Hform (l : ℕ) (P : Poly) (u : ℂ) (x : Space) (i : Fin 3) :
    conj (Hform l P u x i)=-Hform l P (conj u) x i := by
  unfold Hform
  simp only [map_mul,map_div₀,map_neg,map_pow,Complex.conj_ofReal,Complex.conj_I,conj_angularToroidal]
  ring

theorem Eform_lin (l : ℕ) (P : Poly) (s c₁ c₂ u₁ p₁ u₂ p₂ : ℂ) (x : Space) (i : Fin 3) :
    Eform l P s (c₁*u₁+c₂*u₂) (c₁*p₁+c₂*p₂) x i=
      c₁*Eform l P s u₁ p₁ x i+c₂*Eform l P s u₂ p₂ x i := by
  unfold Eform
  ring

theorem Hform_lin (l : ℕ) (P : Poly) (c₁ c₂ u₁ u₂ : ℂ) (x : Space) (i : Fin 3) :
    Hform l P (c₁*u₁+c₂*u₂) x i=c₁*Hform l P u₁ x i+c₂*Hform l P u₂ x i := by
  unfold Hform
  ring

theorem solidE_eq_Eform (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) (i : Fin 3) :
    SolidMaxwellProfiles.electric l P x i=
      Eform l P 1 (regular l ‖x‖ : ℂ) (regularD l ‖x‖ : ℂ) x i := by
  rw [SolidMaxwellProfiles.electric_profile l P hp hh x hx i]
  unfold Eform
  ring

theorem solidH_eq_Hform (l : ℕ) (P : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    SolidMaxwellProfiles.magnetic l P x i=Hform l P (regular l ‖x‖ : ℂ) x i := by
  rw [SolidMaxwellProfiles.magnetic_profile l P x hx i]
  unfold Hform
  ring

theorem xi_add_xiMinus (l : ℕ) (r : ℝ) : xi l (r : ℂ)+xiMinus l (r : ℂ)=2*(regular l r : ℂ) := by
  rw [← xi_conj_real,Complex.add_conj]
  simp [regular]

theorem xiD_add_xiMinusD (l : ℕ) (r : ℝ) :
    xiD l (r : ℂ)+xiMinusD l (r : ℂ)=2*(regularD l r : ℂ) := by
  rw [← xiD_conj_real,Complex.add_conj]
  simp [regularD]

/-- Outgoing vacuum mode formula. -/
def outE (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) : ℂ :=
  Eform l P 1 (xi l (‖x‖ : ℂ)) (xiD l (‖x‖ : ℂ)) x i

/-- Incoming vacuum mode formula. -/
def inE (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) : ℂ :=
  Eform l P 1 (xiMinus l (‖x‖ : ℂ)) (xiMinusD l (‖x‖ : ℂ)) x i

def outH (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) : ℂ := Hform l P (xi l (‖x‖ : ℂ)) x i
def inH (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) : ℂ := Hform l P (xiMinus l (‖x‖ : ℂ)) x i

theorem conj_outE (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) : conj (outE l P x i)=inE l P x i := by
  unfold outE inE
  rw [conj_Eform,map_one,xi_conj_real,xiD_conj_real]

theorem conj_outH (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) : conj (outH l P x i)=-inH l P x i := by
  unfold outH inH
  rw [conj_Hform,xi_conj_real]

theorem outE_add_inE (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) (i : Fin 3) :
    outE l P x i+inE l P x i=2*SolidMaxwellProfiles.electric l P x i := by
  have h := Eform_lin l P 1 1 1 (xi l (‖x‖ : ℂ)) (xiD l (‖x‖ : ℂ))
    (xiMinus l (‖x‖ : ℂ)) (xiMinusD l (‖x‖ : ℂ)) x i
  simp only [one_mul] at h
  rw [xi_add_xiMinus,xiD_add_xiMinusD] at h
  have h2 := Eform_lin l P 1 2 0 (regular l ‖x‖ : ℂ) (regularD l ‖x‖ : ℂ) 0 0 x i
  simp only [zero_mul,add_zero,mul_zero] at h2
  rw [solidE_eq_Eform l P hp hh x hx i]
  unfold outE inE
  linear_combination h2-h

theorem outH_add_inH (l : ℕ) (P : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    outH l P x i+inH l P x i=2*SolidMaxwellProfiles.magnetic l P x i := by
  have h := Hform_lin l P 1 1 (xi l (‖x‖ : ℂ)) (xiMinus l (‖x‖ : ℂ)) x i
  simp only [one_mul] at h
  rw [xi_add_xiMinus] at h
  have h2 := Hform_lin l P 2 0 (regular l ‖x‖ : ℂ) 0 x i
  simp only [zero_mul,add_zero,mul_zero] at h2
  rw [solidH_eq_Hform l P x hx i]
  unfold outH inH
  linear_combination h2-h

theorem conj_solidE (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) (i : Fin 3) :
    conj (SolidMaxwellProfiles.electric l P x i)=SolidMaxwellProfiles.electric l P x i := by
  rw [solidE_eq_Eform l P hp hh x hx i,conj_Eform]
  simp [Complex.conj_ofReal]

theorem conj_solidH (l : ℕ) (P : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    conj (SolidMaxwellProfiles.magnetic l P x i)=-SolidMaxwellProfiles.magnetic l P x i := by
  rw [solidH_eq_Hform l P x hx i,conj_Hform]
  simp [Complex.conj_ofReal]

end Formulas


theorem testForced_sub (k : ℝ) (ρ ρ' : Fin 3 → Space → ℂ) (E H E' H' : Field)
    (hρ : ∀ i, LocallyIntegrable (ρ i)) (hρ' : ∀ i, LocallyIntegrable (ρ' i))
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hE' : ∀ i, LocallyIntegrable (fun x => E' x i)) (hH' : ∀ i, LocallyIntegrable (fun x => H' x i))
    (h : TestForced k ρ E H) (h' : TestForced k ρ' E' H') :
    TestForced k (fun i x => ρ i x-ρ' i x) (E-E') (H-H') := by
  intro i f
  obtain ⟨a1,a2⟩ := h i f
  obtain ⟨b1,b2⟩ := h' i f
  have hi : (∫ x,(ρ i x-ρ' i x)*f.val x)=(∫ x,ρ i x*f.val x)-∫ x,ρ' i x*f.val x := by
    simp only [sub_mul]
    exact integral_sub (PointSingularity.test_product_integrable _ _ (hρ i) f.val.continuous f.property)
      (PointSingularity.test_product_integrable _ _ (hρ' i) f.val.continuous f.property)
  constructor
  · have hc : curlPair (fieldPair (E-E')) i f=curlPair (fieldPair E) i f-curlPair (fieldPair E') i f := by
      rw [← curlPair_sub]
      congr 1
      funext j g
      exact fieldPair_sub E E' hE hE' j g
    rw [hc,a1,b1,fieldPair_sub H H' hH hH']
    ring
  · have hc : curlPair (fieldPair (H-H')) i f=curlPair (fieldPair H) i f-curlPair (fieldPair H') i f := by
      rw [← curlPair_sub]
      congr 1
      funext j g
      exact fieldPair_sub H H' hH hH' j g
    rw [hc,a2,b2,fieldPair_sub E E' hE hE',hi]
    ring

theorem testForced_congr_rho (k : ℝ) (ρ τ : Fin 3 → Space → ℂ) (E H : Field)
    (h : ∀ i, ρ i=ᵐ[volume] τ i) (hf : TestForced k ρ E H) : TestForced k τ E H := by
  intro i f
  obtain ⟨a1,a2⟩ := hf i f
  have : (∫ x,τ i x*f.val x)=∫ x,ρ i x*f.val x := by
    apply integral_congr_ae
    filter_upwards [h i] with x hx
    rw [hx]
  rw [this]
  exact ⟨a1,a2⟩

/-! ### The background fields of a layered stack -/

section Background
open OQ14.HarmonicPolynomial OQ14.SourceRadialSystem OQ14.SourceCoreReaction OQ14.HankelRealBasis
  OQ14.ModalAlgebra OQ14.BackgroundCoreTransmission

/-- `kappa d = -conj c.2 / 2`: the half normalization of the amplitude-two states. -/
def kappa (d : Data) : ℂ :=
  -(conj (OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2)/2

theorem two_kappa (d : Data) :
    2*kappa d=-(conj (OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2) := by
  unfold kappa; ring

theorem hX_pos (d : Data) : 0<d.X := d.hR.trans_le (RadialStack.chain_ordered d.chain)

/-- Background electric field, built from the global regular source correction. -/
def backgroundElectric (d : Data) (P : Poly) : Field :=
  kappa d • (SourceRegularCorrection.electric d P-conjField (SourceRegularCorrection.electric d P))+
    (-2*Complex.I*kappa d) • SolidMaxwellProfiles.electric d.l P

/-- Background magnetic field. -/
def backgroundMagnetic (d : Data) (P : Poly) : Field :=
  kappa d • (SourceRegularCorrection.magnetic d P+conjField (SourceRegularCorrection.magnetic d P))+
    (-2*Complex.I*kappa d) • SolidMaxwellProfiles.magnetic d.l P

/-- Polarization of the background electric field. -/
def backgroundPolarization (d : Data) (P : Poly) (i : Fin 3) (x : Space) : ℂ :=
  kappa d*(SourceRegularCorrection.polarization d P i x-
    conj (SourceRegularCorrection.polarization d P i x))

theorem inverseSigma_vacuum (d : Data) (r : ℝ) : inverseSigma (vacuum d) r=1 := by
  simp only [inverseSigma,SourceRadialSystem.extend,vacuum]
  split_ifs <;> simp_all

theorem inverseSigma_exterior (d : Data) (r : ℝ) (hr : d.X<r) : inverseSigma d r=1 := by
  have hR : d.R<r := lt_of_le_of_lt (RadialStack.chain_ordered d.chain) hr
  simp only [inverseSigma,SourceRadialSystem.extend,if_neg (not_le.mpr hR),if_neg (not_le.mpr hr)]

theorem conj_sigma (d : Data) (r : ℝ) : conj (sigma d r)=sigma d r := by
  unfold sigma SourceRadialSystem.extend
  split_ifs <;> simp

/-- The vacuum source electric field is `-I` times the outgoing mode formula. -/
theorem vacE_eq (d : Data) (P : Poly) (x : Space) (i : Fin 3) :
    SourceUnclippedMaxwell.electric (vacuum d) P x i=-Complex.I*outE d.l P x i := by
  rw [electric_eq_Eform,inverseSigma_vacuum,vacuum_raw]
  have h := Eform_lin d.l P 1 (-Complex.I) 0 (xi d.l (‖x‖ : ℂ)) (xiD d.l (‖x‖ : ℂ)) 0 0 x i
  simp only [zero_mul,add_zero,mul_zero] at h
  unfold outE
  simpa [RadialStack.outgoing,vacuum] using h

theorem vacH_eq (d : Data) (P : Poly) (x : Space) (i : Fin 3) :
    SourceUnclippedMaxwell.magnetic (vacuum d) P x i=-Complex.I*outH d.l P x i := by
  rw [magnetic_eq_Hform,vacuum_raw]
  have h := Hform_lin d.l P (-Complex.I) 0 (xi d.l (‖x‖ : ℂ)) 0 x i
  simp only [zero_mul,add_zero,mul_zero] at h
  unfold outH
  simpa [RadialStack.outgoing,vacuum] using h

theorem vacE_conj_sub (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) (i : Fin 3) :
    SourceUnclippedMaxwell.electric (vacuum d) P x i-conj (SourceUnclippedMaxwell.electric (vacuum d) P x i)=
      -2*Complex.I*SolidMaxwellProfiles.electric d.l P x i := by
  rw [vacE_eq,map_mul,conj_outE,Complex.conj_neg_I]
  have h := outE_add_inE d.l P hp hh x hx i
  linear_combination -Complex.I*h

theorem vacH_conj_add (d : Data) (P : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    SourceUnclippedMaxwell.magnetic (vacuum d) P x i+conj (SourceUnclippedMaxwell.magnetic (vacuum d) P x i)=
      -2*Complex.I*SolidMaxwellProfiles.magnetic d.l P x i := by
  rw [vacH_eq,map_mul,conj_outH,Complex.conj_neg_I]
  have h := outH_add_inH d.l P x hx i
  linear_combination -Complex.I*h

/-- Away from the origin the background electric field is `kappa * (E - conj E)` of the source mode. -/
theorem backgroundElectric_eq (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) (i : Fin 3) :
    backgroundElectric d P x i=kappa d*(SourceUnclippedMaxwell.electric d P x i-
      conj (SourceUnclippedMaxwell.electric d P x i)) := by
  have hc := congrFun (SourceRegularCorrection.electric_away d P hp hh x hx) i
  have hv := vacE_conj_sub d P hp hh x hx i
  simp only [Pi.sub_apply] at hc
  simp only [backgroundElectric,conjField,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  rw [hc,map_sub]
  linear_combination -kappa d*hv

theorem backgroundMagnetic_eq (d : Data) (P : Poly) (x : Space) (hx : x≠0) (i : Fin 3) :
    backgroundMagnetic d P x i=kappa d*(SourceUnclippedMaxwell.magnetic d P x i+
      conj (SourceUnclippedMaxwell.magnetic d P x i)) := by
  have hc := congrFun (SourceRegularCorrection.magnetic_away d P x hx) i
  have hv := vacH_conj_add d P x hx i
  simp only [Pi.sub_apply] at hc
  simp only [backgroundMagnetic,conjField,Pi.add_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul]
  rw [hc,map_sub]
  linear_combination -kappa d*hv

/-- **Core.**  Inside the core the background electric field is `transmission/2` times the regular
vacuum mode. -/
theorem backgroundElectric_core (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) (hR : ‖x‖≤d.R) :
    backgroundElectric d P x=(transmission d.l d.gs d.R d.X d.hR/2) • SolidMaxwellProfiles.electric d.l P x := by
  ext i
  rw [backgroundElectric_eq d P hp hh x hx i]
  have hd := congrFun (electric_core_difference d P hp hh x hx hR) i
  have hv := vacE_conj_sub d P hp hh x hx i
  have hr := conj_solidE d.l P hp hh x hx i
  have hk := kappa_gamma d.l d.gs d.R d.X d.hR (hX_pos d)
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hd
  have he : SourceUnclippedMaxwell.electric d P x i=
      SourceUnclippedMaxwell.electric (vacuum d) P x i+multiplier d*SolidMaxwellProfiles.electric d.l P x i := by
    linear_combination hd
  rw [he,map_add,map_mul,hr]
  simp only [Pi.smul_apply,smul_eq_mul]
  have hmu : conj (multiplier d)=conj (OQ14.RadialSource.gamma d.l d.gs d.R d.X d.hR)-Complex.I := by
    unfold multiplier
    rw [map_add,Complex.conj_I]; ring
  rw [hmu]
  have h2 := two_kappa d
  unfold multiplier
  linear_combination kappa d*hv+SolidMaxwellProfiles.electric d.l P x i*
    ((1/2)*(OQ14.RadialSource.gamma d.l d.gs d.R d.X d.hR-conj (OQ14.RadialSource.gamma d.l d.gs d.R d.X d.hR))*h2+(1/2)*hk)

theorem backgroundMagnetic_core (d : Data) (P : Poly) (x : Space) (hx : x≠0) (hR : ‖x‖≤d.R) :
    backgroundMagnetic d P x=(transmission d.l d.gs d.R d.X d.hR/2) • SolidMaxwellProfiles.magnetic d.l P x := by
  ext i
  rw [backgroundMagnetic_eq d P x hx i]
  have hd := congrFun (magnetic_core_difference d P x hx hR) i
  have hv := vacH_conj_add d P x hx i
  have hr := conj_solidH d.l P x hx i
  have hk := kappa_gamma d.l d.gs d.R d.X d.hR (hX_pos d)
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul] at hd
  have he : SourceUnclippedMaxwell.magnetic d P x i=
      SourceUnclippedMaxwell.magnetic (vacuum d) P x i+multiplier d*SolidMaxwellProfiles.magnetic d.l P x i := by
    linear_combination hd
  rw [he,map_add,map_mul,hr]
  simp only [Pi.smul_apply,smul_eq_mul]
  have hmu : conj (multiplier d)=conj (OQ14.RadialSource.gamma d.l d.gs d.R d.X d.hR)-Complex.I := by
    unfold multiplier
    rw [map_add,Complex.conj_I]; ring
  rw [hmu]
  have h2 := two_kappa d
  unfold multiplier
  linear_combination kappa d*hv+SolidMaxwellProfiles.magnetic d.l P x i*
    ((1/2)*(OQ14.RadialSource.gamma d.l d.gs d.R d.X d.hR-conj (OQ14.RadialSource.gamma d.l d.gs d.R d.X d.hR))*h2+(1/2)*hk)

end Background


section Background2
open OQ14.HarmonicPolynomial OQ14.SourceRadialSystem OQ14.SourceCoreReaction OQ14.HankelRealBasis
  OQ14.ModalAlgebra OQ14.BackgroundCoreTransmission

theorem locallyIntegrable_sub' (E F : Field) (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (i : Fin 3) :
    LocallyIntegrable (fun x => (E-F) x i) := by
  simpa only [Pi.sub_apply] using (hE i).sub (hF i)

theorem solidE_locallyIntegrable (l : ℕ) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SolidMaxwellProfiles.electric l P x i) :=
  (SolidMaxwellProfiles.electric_smooth l P i).continuous.locallyIntegrable

theorem solidH_locallyIntegrable (l : ℕ) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SolidMaxwellProfiles.magnetic l P x i) :=
  (SolidMaxwellProfiles.magnetic_smooth l P i).continuous.locallyIntegrable

theorem backgroundElectric_locallyIntegrable (d : Data) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => backgroundElectric d P x i) := by
  have h1 := SourceCorrectionLocalBounds.electric_locallyIntegrable d P
  exact locallyIntegrable_add _ _
    (locallyIntegrable_smul _ _ (locallyIntegrable_sub' _ _ h1 (locallyIntegrable_conj _ h1)))
    (locallyIntegrable_smul _ _ (solidE_locallyIntegrable d.l P)) i

theorem backgroundMagnetic_locallyIntegrable (d : Data) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => backgroundMagnetic d P x i) := by
  have h1 := SourceCorrectionLocalBounds.magnetic_locallyIntegrable d P
  exact locallyIntegrable_add _ _
    (locallyIntegrable_smul _ _ (locallyIntegrable_add _ _ h1 (locallyIntegrable_conj _ h1)))
    (locallyIntegrable_smul _ _ (solidH_locallyIntegrable d.l P)) i

/-- **Weak Maxwell for the background pair.**  The pair `(backgroundElectric, backgroundMagnetic)` solves the
forced Maxwell equations with the polarization `backgroundPolarization` against every Schwartz test
function of compact support, across the origin. -/
theorem background_forced (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) :
    TestForced 1 (backgroundPolarization d P) (backgroundElectric d P) (backgroundMagnetic d P) := by
  have hc := SourceGlobalCorrection.forced_maxwell d hdisp P hp hh
  have hcc := testForced_conj 1 _ _ _ hc
  have hEc := SourceCorrectionLocalBounds.electric_locallyIntegrable d P
  have hHc := SourceCorrectionLocalBounds.magnetic_locallyIntegrable d P
  have hρc : ∀ i, LocallyIntegrable (SourceRegularCorrection.polarization d P i) :=
    fun i => (SourceCorrectionLocalBounds.polarization_integrable d P i).locallyIntegrable
  have hρcc : ∀ i, LocallyIntegrable (fun x => conj (SourceRegularCorrection.polarization d P i x)) := by
    intro i
    refine (hρc i).mono (Complex.continuous_conj.comp_aestronglyMeasurable (hρc i).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun x => by simp)
  have hsub := testForced_sub 1 _ _ _ _ _ _ hρc hρcc hEc hHc (locallyIntegrable_conj _ hEc)
    (locallyIntegrable_negConj _ hHc) hc hcc
  have hE1 : ∀ i, LocallyIntegrable (fun x => (SourceRegularCorrection.electric d P-
      conjField (SourceRegularCorrection.electric d P)) x i) :=
    locallyIntegrable_sub' _ _ hEc (locallyIntegrable_conj _ hEc)
  have hH1 : ∀ i, LocallyIntegrable (fun x => (SourceRegularCorrection.magnetic d P-
      negConjField (SourceRegularCorrection.magnetic d P)) x i) :=
    locallyIntegrable_sub' _ _ hHc (locallyIntegrable_negConj _ hHc)
  have hsm := testForced_smul 1 (kappa d) _ _ _ hsub
  have hvac := TestFieldLocalization.vacuum_smul (-2*Complex.I*kappa d) 1 (SolidMaxwellProfiles.electric d.l P)
    (SolidMaxwellProfiles.magnetic d.l P)
    (MaterialMaxwell.classical_vacuum_testMaxwell 1 _ _
      (fun i => (SolidMaxwellProfiles.electric_smooth d.l P i).of_le (by simp))
      (fun i => (SolidMaxwellProfiles.magnetic_smooth d.l P i).of_le (by simp))
      (SolidMaxwellProfiles.actual_maxwell d.l P hp hh))
  have hρk : ∀ i, LocallyIntegrable (fun x => kappa d*(SourceRegularCorrection.polarization d P i x-
      conj (SourceRegularCorrection.polarization d P i x))) := fun i => by
    simpa only [smul_eq_mul] using ((hρc i).sub (hρcc i)).smul (kappa d)
  have hadd := testForced_add 1 _ _ _ _ _ _ hρk
    (fun i => locallyIntegrable_zero) (locallyIntegrable_smul _ _ hE1) (locallyIntegrable_smul _ _ hH1)
    (locallyIntegrable_smul _ _ (solidE_locallyIntegrable d.l P))
    (locallyIntegrable_smul _ _ (solidH_locallyIntegrable d.l P))
    hsm hvac
  have e1 : (SourceRegularCorrection.magnetic d P-negConjField (SourceRegularCorrection.magnetic d P))=
      SourceRegularCorrection.magnetic d P+conjField (SourceRegularCorrection.magnetic d P) := by
    funext x i
    simp [negConjField,conjField]
  rw [e1] at hadd
  have e0 : backgroundPolarization d P=fun i x => kappa d*(SourceRegularCorrection.polarization d P i x-
      conj (SourceRegularCorrection.polarization d P i x))+0 := by
    funext i x
    simp [backgroundPolarization]
  rw [e0]
  exact hadd

end Background2


section Background3
open OQ14.HarmonicPolynomial OQ14.SourceRadialSystem OQ14.SourceCoreReaction OQ14.HankelRealBasis
  OQ14.ModalAlgebra OQ14.BackgroundCoreTransmission

theorem x_ne_zero_of_exterior (d : Data) (x : Space) (hx : d.X<‖x‖) : x≠0 := by
  intro h
  rw [h,norm_zero] at hx
  exact absurd hx (not_lt.mpr (hX_pos d).le)

/-- Beyond `X` the source electric field is `c.2⁻¹` times the outgoing mode formula. -/
theorem electric_exterior (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    SourceUnclippedMaxwell.electric d P x i=
      ((OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2)⁻¹*outE d.l P x i := by
  rw [electric_eq_Eform,inverseSigma_exterior d _ hx]
  have hs : raw d ‖x‖=((OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2)⁻¹ •
      RadialStack.outgoing d.l ‖x‖ := OQ14.RadialGluing.sourceState_exterior d.l d.chain d.hR ‖x‖ hx
  rw [hs]
  have h := Eform_lin d.l P 1 ((OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2)⁻¹ 0
    (xi d.l (‖x‖ : ℂ)) (xiD d.l (‖x‖ : ℂ)) 0 0 x i
  simp only [zero_mul,add_zero,mul_zero] at h
  unfold outE
  simpa [RadialStack.outgoing] using h

theorem magnetic_exterior (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    SourceUnclippedMaxwell.magnetic d P x i=
      ((OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2)⁻¹*outH d.l P x i := by
  rw [magnetic_eq_Hform]
  have hs : raw d ‖x‖=((OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2)⁻¹ •
      RadialStack.outgoing d.l ‖x‖ := OQ14.RadialGluing.sourceState_exterior d.l d.chain d.hR ‖x‖ hx
  rw [hs]
  have h := Hform_lin d.l P ((OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2)⁻¹ 0
    (xi d.l (‖x‖ : ℂ)) 0 x i
  simp only [zero_mul,add_zero,mul_zero] at h
  unfold outH
  simpa [RadialStack.outgoing] using h

theorem exterior_algebra (r F : ℂ) : ((r-1)/2*Complex.I)*(-Complex.I*F)=(r-1)/2*F := by
  linear_combination (-((r-1)/2*F))*Complex.I_mul_I

/-- **Exterior.**  Beyond `X` the background electric field is the regular vacuum mode plus
`(reflection - 1)/2` times the outgoing vacuum mode (`I` times the vacuum source field). -/
theorem backgroundElectric_exterior (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : d.X<‖x‖) :
    backgroundElectric d P x=SolidMaxwellProfiles.electric d.l P x+
      (((reflection d.l d.gs d.R d.X d.hR-1)/2*Complex.I) •
        SourceUnclippedMaxwell.electric (vacuum d) P x) := by
  have hx0 := x_ne_zero_of_exterior d x hx
  ext i
  have hc2 := OQ14.RadialSource.coefficients_second_ne_zero d.l d.gs d.R d.X d.hR (hX_pos d)
  have hc2b : conj (OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2≠0 :=
    (map_ne_zero _).mpr hc2
  have hin := outE_add_inE d.l P hp hh x hx0 i
  have hin' : inE d.l P x i=2*SolidMaxwellProfiles.electric d.l P x i-outE d.l P x i := by
    linear_combination hin
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [backgroundElectric_eq d P hp hh x hx0 i,electric_exterior d P x hx i,map_mul,map_inv₀,
    conj_outE,vacE_eq,hin',exterior_algebra]
  unfold kappa reflection
  field_simp
  ring

theorem backgroundMagnetic_exterior (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) :
    backgroundMagnetic d P x=SolidMaxwellProfiles.magnetic d.l P x+
      (((reflection d.l d.gs d.R d.X d.hR-1)/2*Complex.I) •
        SourceUnclippedMaxwell.magnetic (vacuum d) P x) := by
  have hx0 := x_ne_zero_of_exterior d x hx
  ext i
  have hc2 := OQ14.RadialSource.coefficients_second_ne_zero d.l d.gs d.R d.X d.hR (hX_pos d)
  have hc2b : conj (OQ14.RadialSource.coefficients d.l d.gs d.R d.X d.hR).2≠0 :=
    (map_ne_zero _).mpr hc2
  have hin := outH_add_inH d.l P x hx0 i
  have hin' : inH d.l P x i=2*SolidMaxwellProfiles.magnetic d.l P x i-outH d.l P x i := by
    linear_combination hin
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [backgroundMagnetic_eq d P x hx0 i,magnetic_exterior d P x hx i,map_mul,map_inv₀,
    conj_outH,vacH_eq,hin',exterior_algebra]
  unfold kappa reflection
  field_simp
  ring

/-- The background force is `(sigma - 1)` times the background electric field. -/
theorem backgroundPolarization_eq (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian P=0) (x : Space) (hx : x≠0) (i : Fin 3) :
    backgroundPolarization d P i x=(sigma d ‖x‖-1)*backgroundElectric d P x i := by
  rw [backgroundElectric_eq d P hp hh x hx i]
  unfold backgroundPolarization SourceRegularCorrection.polarization
  rw [map_mul,map_sub,conj_sigma,map_one]
  ring

/-- Background pair with the force written as `(sigma - 1) E`. -/
theorem background_forced_sigma (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (P : Poly)
    (hp : P.IsHomogeneous d.l) (hh : HarmonicPolynomial.formalLaplacian P=0) :
    TestForced 1 (fun i x => (sigma d ‖x‖-1)*backgroundElectric d P x i) (backgroundElectric d P)
      (backgroundMagnetic d P) := by
  apply testForced_congr_rho 1 (backgroundPolarization d P) _ _ _ _ (background_forced d hdisp P hp hh)
  intro i
  filter_upwards [show ∀ᵐ x : Space, x≠0 from ae_iff.mpr (by simp)] with x hx
  exact backgroundPolarization_eq d P hp hh x hx i

end Background3

end OQ14.BackgroundModeMaxwell
#print axioms OQ14.BackgroundModeMaxwell.dcoord_conj
#print axioms OQ14.BackgroundModeMaxwell.dcoord_real
#print axioms OQ14.BackgroundModeMaxwell.conj_contDiff
#print axioms OQ14.BackgroundModeMaxwell.conj_compact
#print axioms OQ14.BackgroundModeMaxwell.conjTest_apply
#print axioms OQ14.BackgroundModeMaxwell.testPartial_conjTest
#print axioms OQ14.BackgroundModeMaxwell.fieldPair_conj
#print axioms OQ14.BackgroundModeMaxwell.fieldPair_negConj
#print axioms OQ14.BackgroundModeMaxwell.curlPair_conj
#print axioms OQ14.BackgroundModeMaxwell.curlPair_negConj
#print axioms OQ14.BackgroundModeMaxwell.integral_conj_pair
#print axioms OQ14.BackgroundModeMaxwell.testForced_conj
#print axioms OQ14.BackgroundModeMaxwell.fieldPair_add
#print axioms OQ14.BackgroundModeMaxwell.curlPair_add
#print axioms OQ14.BackgroundModeMaxwell.locallyIntegrable_smul
#print axioms OQ14.BackgroundModeMaxwell.locallyIntegrable_add
#print axioms OQ14.BackgroundModeMaxwell.locallyIntegrable_conj
#print axioms OQ14.BackgroundModeMaxwell.locallyIntegrable_negConj
#print axioms OQ14.BackgroundModeMaxwell.testForced_add
#print axioms OQ14.BackgroundModeMaxwell.testForced_smul
#print axioms OQ14.BackgroundModeMaxwell.electric_eq_Eform
#print axioms OQ14.BackgroundModeMaxwell.magnetic_eq_Hform
#print axioms OQ14.BackgroundModeMaxwell.conj_cE
#print axioms OQ14.BackgroundModeMaxwell.conj_dcoord_cE
#print axioms OQ14.BackgroundModeMaxwell.conj_angularToroidal
#print axioms OQ14.BackgroundModeMaxwell.conj_Eform
#print axioms OQ14.BackgroundModeMaxwell.conj_Hform
#print axioms OQ14.BackgroundModeMaxwell.Eform_lin
#print axioms OQ14.BackgroundModeMaxwell.Hform_lin
#print axioms OQ14.BackgroundModeMaxwell.solidE_eq_Eform
#print axioms OQ14.BackgroundModeMaxwell.solidH_eq_Hform
#print axioms OQ14.BackgroundModeMaxwell.xi_add_xiMinus
#print axioms OQ14.BackgroundModeMaxwell.xiD_add_xiMinusD
#print axioms OQ14.BackgroundModeMaxwell.conj_outE
#print axioms OQ14.BackgroundModeMaxwell.conj_outH
#print axioms OQ14.BackgroundModeMaxwell.outE_add_inE
#print axioms OQ14.BackgroundModeMaxwell.outH_add_inH
#print axioms OQ14.BackgroundModeMaxwell.conj_solidE
#print axioms OQ14.BackgroundModeMaxwell.conj_solidH
#print axioms OQ14.BackgroundModeMaxwell.testForced_sub
#print axioms OQ14.BackgroundModeMaxwell.testForced_congr_rho
#print axioms OQ14.BackgroundModeMaxwell.two_kappa
#print axioms OQ14.BackgroundModeMaxwell.hX_pos
#print axioms OQ14.BackgroundModeMaxwell.inverseSigma_vacuum
#print axioms OQ14.BackgroundModeMaxwell.inverseSigma_exterior
#print axioms OQ14.BackgroundModeMaxwell.conj_sigma
#print axioms OQ14.BackgroundModeMaxwell.vacE_eq
#print axioms OQ14.BackgroundModeMaxwell.vacH_eq
#print axioms OQ14.BackgroundModeMaxwell.vacE_conj_sub
#print axioms OQ14.BackgroundModeMaxwell.vacH_conj_add
#print axioms OQ14.BackgroundModeMaxwell.backgroundElectric_eq
#print axioms OQ14.BackgroundModeMaxwell.backgroundMagnetic_eq
#print axioms OQ14.BackgroundModeMaxwell.backgroundElectric_core
#print axioms OQ14.BackgroundModeMaxwell.backgroundMagnetic_core
#print axioms OQ14.BackgroundModeMaxwell.locallyIntegrable_sub'
#print axioms OQ14.BackgroundModeMaxwell.solidE_locallyIntegrable
#print axioms OQ14.BackgroundModeMaxwell.solidH_locallyIntegrable
#print axioms OQ14.BackgroundModeMaxwell.backgroundElectric_locallyIntegrable
#print axioms OQ14.BackgroundModeMaxwell.backgroundMagnetic_locallyIntegrable
#print axioms OQ14.BackgroundModeMaxwell.background_forced
#print axioms OQ14.BackgroundModeMaxwell.x_ne_zero_of_exterior
#print axioms OQ14.BackgroundModeMaxwell.electric_exterior
#print axioms OQ14.BackgroundModeMaxwell.magnetic_exterior
#print axioms OQ14.BackgroundModeMaxwell.exterior_algebra
#print axioms OQ14.BackgroundModeMaxwell.backgroundElectric_exterior
#print axioms OQ14.BackgroundModeMaxwell.backgroundMagnetic_exterior
#print axioms OQ14.BackgroundModeMaxwell.backgroundPolarization_eq
#print axioms OQ14.BackgroundModeMaxwell.background_forced_sigma
