import CoreWeakSeries



/-! Linear algebra of the weak first Maxwell equation on an open set: scaling, congruence on the set, and
the rotation combination used for the electric and magnetic parts of polarized mode pairs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CoreWeakLinear
open MeasureTheory Filter Set Metric Complex OQ14.Maxwell OQ14.SourceRemotePlaneBand OQ14.CoreWeakSeries
  OQ14.BackgroundModeMaxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open scoped Topology ComplexConjugate

/-! ### Linear algebra of the weak equation -/

theorem fieldPair_const_mul (c : ℂ) (F : Field) (j : Fin 3) (g : DynamicSource.Test) :
    MaterialMaxwell.fieldPair (fun x i => c * F x i) j g = c * MaterialMaxwell.fieldPair F j g := by
  unfold MaterialMaxwell.fieldPair
  simp_rw [mul_assoc]
  exact integral_const_mul c _

theorem curlPair_const_mul (c : ℂ) (F : Field) (i : Fin 3) (g : DynamicSource.Test) :
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair (fun x i => c * F x i)) i g =
      c * MagneticResponse.curlPair (MaterialMaxwell.fieldPair F) i g := by
  unfold MagneticResponse.curlPair
  rw [fieldPair_const_mul, fieldPair_const_mul]
  ring

theorem weakOn_of_scaled {Ω : Set Space} {E H : Field} (c : ℂ) (hc : c ≠ 0) (E2 H2 : Field)
    (hE : ∀ x i, E2 x i = c * E x i) (hH : ∀ x i, H2 x i = c * H x i) (h : WeakOn Ω E2 H2) :
    WeakOn Ω E H := by
  intro i f hf
  have hE' : E2 = fun x i => c * E x i := funext fun x => funext fun i => hE x i
  have hH' : H2 = fun x i => c * H x i := funext fun x => funext fun i => hH x i
  have := h i f hf
  rw [hE', hH', curlPair_const_mul, fieldPair_const_mul] at this
  exact mul_left_cancel₀ hc (by rw [this]; ring)

theorem weakOn_congr {Ω : Set Space} {E E2 H H2 : Field} (hE : ∀ x ∈ Ω, ∀ i, E x i = E2 x i)
    (hH : ∀ x ∈ Ω, ∀ i, H x i = H2 x i) (h : WeakOn Ω E H) : WeakOn Ω E2 H2 := by
  intro i f hf
  have hz : ∀ x, x ∉ Ω → f.val x = 0 := fun x hx => image_eq_zero_of_nmem_tsupport (fun h => hx (hf h))
  have hp (F F2 : Field) (hFF : ∀ x ∈ Ω, ∀ i, F x i = F2 x i) (j : Fin 3) (g : DynamicSource.Test)
      (hg : ∀ x, x ∉ Ω → g.val x = 0) :
      MaterialMaxwell.fieldPair F j g = MaterialMaxwell.fieldPair F2 j g := by
    unfold MaterialMaxwell.fieldPair
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Ω
    · rw [hFF x hx j]
    · simp [hg x hx]
  have hg1 : ∀ x, x ∉ Ω → (DynamicSource.testPartial (WeakCurl.previous i) f).val x = 0 := fun x hx =>
    image_eq_zero_of_nmem_tsupport (fun h => hx (hf ((tsupport_testPartial_subset _ f) h)))
  have hg2 : ∀ x, x ∉ Ω → (DynamicSource.testPartial (WeakCurl.next i) f).val x = 0 := fun x hx =>
    image_eq_zero_of_nmem_tsupport (fun h => hx (hf ((tsupport_testPartial_subset _ f) h)))
  have := h i f hf
  unfold MagneticResponse.curlPair at this ⊢
  rw [hp E E2 hE _ _ hg1, hp E E2 hE _ _ hg2, hp H H2 hH _ _ hz] at this
  exact this

theorem weakOn_combo {Ω : Set Space} (E H : Field) (α β : ℂ)
    (hEc : ∀ j, ContinuousOn (fun x => E x j) Ω) (hHc : ∀ j, ContinuousOn (fun x => H x j) Ω)
    (h1 : WeakOn Ω E H) (h2 : WeakOn Ω H (fun x i => -E x i)) :
    WeakOn Ω (fun x i => α * E x i + β * H x i) (fun x i => α * H x i - β * E x i) := by
  intro i f hf
  have hadd (F G : Field) (a b : ℂ) (hF : ∀ j, ContinuousOn (fun x => F x j) Ω)
      (hG : ∀ j, ContinuousOn (fun x => G x j) Ω) (j : Fin 3) (g : DynamicSource.Test)
      (hg : tsupport (g.val : Space → ℂ) ⊆ Ω) :
      MaterialMaxwell.fieldPair (fun x i => a * F x i + b * G x i) j g =
        a * MaterialMaxwell.fieldPair F j g + b * MaterialMaxwell.fieldPair G j g := by
    unfold MaterialMaxwell.fieldPair
    have i1 := integrable_mul_test (fun x => F x j) (hF j) g hg
    have i2 := integrable_mul_test (fun x => G x j) (hG j) g hg
    have : (fun x => (a * F x j + b * G x j) * g.val x) =
        fun x => a * (F x j * g.val x) + b * (G x j * g.val x) := by funext x; ring
    rw [this, integral_add (i1.const_mul a) (i2.const_mul b), integral_const_mul, integral_const_mul]
  have hsub (F G : Field) (a b : ℂ) (hF : ∀ j, ContinuousOn (fun x => F x j) Ω)
      (hG : ∀ j, ContinuousOn (fun x => G x j) Ω) (j : Fin 3) (g : DynamicSource.Test)
      (hg : tsupport (g.val : Space → ℂ) ⊆ Ω) :
      MaterialMaxwell.fieldPair (fun x i => a * F x i - b * G x i) j g =
        a * MaterialMaxwell.fieldPair F j g - b * MaterialMaxwell.fieldPair G j g := by
    unfold MaterialMaxwell.fieldPair
    have i1 := integrable_mul_test (fun x => F x j) (hF j) g hg
    have i2 := integrable_mul_test (fun x => G x j) (hG j) g hg
    have : (fun x => (a * F x j - b * G x j) * g.val x) =
        fun x => a * (F x j * g.val x) - b * (G x j * g.val x) := by funext x; ring
    rw [this, integral_sub (i1.const_mul a) (i2.const_mul b), integral_const_mul, integral_const_mul]
  have hg1 : tsupport ((DynamicSource.testPartial (WeakCurl.previous i) f).val : Space → ℂ) ⊆ Ω :=
    (tsupport_testPartial_subset _ f).trans hf
  have hg2 : tsupport ((DynamicSource.testPartial (WeakCurl.next i) f).val : Space → ℂ) ⊆ Ω :=
    (tsupport_testPartial_subset _ f).trans hf
  have hnE : ∀ j, ContinuousOn (fun x => -E x j) Ω := fun j => (hEc j).neg
  have e1 := h1 i f hf
  have e2 := h2 i f hf
  have hpm : MaterialMaxwell.fieldPair (fun x i => -E x i) i f = -MaterialMaxwell.fieldPair E i f := by
    have := fieldPair_const_mul (-1 : ℂ) E i f
    simpa using this
  rw [hpm] at e2
  unfold MagneticResponse.curlPair at e1 e2 ⊢
  rw [hadd E H α β hEc hHc _ _ hg1, hadd E H α β hEc hHc _ _ hg2, hsub H E α β hHc hEc i f hf]
  linear_combination α * e1 + β * e2

end OQ14.CoreWeakLinear

#print axioms OQ14.CoreWeakLinear.fieldPair_const_mul
#print axioms OQ14.CoreWeakLinear.curlPair_const_mul
#print axioms OQ14.CoreWeakLinear.weakOn_of_scaled
#print axioms OQ14.CoreWeakLinear.weakOn_congr
#print axioms OQ14.CoreWeakLinear.weakOn_combo
