import SourceLocalBounds
import TestFieldLocalization

/-! Integrability of genuine punctured source fields against tests away from the source point. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceTestIntegrals
open MeasureTheory Set OQ14.Maxwell OQ14.SourceRadialSystem OQ14.DynamicSource OQ14.MaterialMaxwell
open OQ14.MagneticResponse OQ14.SourceUnclippedMaxwell

theorem product_integrable (u v : Space → ℂ) (hv : LocallyIntegrable v) (f : Test)
    (he : ∀ x∈tsupport (f.val : Space → ℂ),u x=v x) : Integrable (fun x => u x*f.val x) := by
  apply (PointSingularity.test_product_integrable v f.val hv f.val.continuous f.property).congr
  filter_upwards with x
  by_cases hx : x∈tsupport (f.val : Space → ℂ)
  · rw [he x hx]
  · rw [image_eq_zero_of_nmem_tsupport hx,mul_zero,mul_zero]

theorem electric_integrable (d : Data) (p : HarmonicPolynomial.Poly) (f : Test)
    (h0 : (0 : Space)∉tsupport (f.val : Space → ℂ)) (i : Fin 3) :
    Integrable (fun x => electric d p x i*f.val x) := by
  obtain ⟨c,hc,hs⟩ := compact_test_gap f.val h0
  exact product_integrable _ _ (SourceLocalBounds.electric_locallyIntegrable (reclip d c hc) p i) f
    (fun x hx => (congrFun (electric_agrees d c hc p x (hs hx)) i).symm)

theorem magnetic_integrable (d : Data) (p : HarmonicPolynomial.Poly) (f : Test)
    (h0 : (0 : Space)∉tsupport (f.val : Space → ℂ)) (i : Fin 3) :
    Integrable (fun x => magnetic d p x i*f.val x) := by
  obtain ⟨c,hc,hs⟩ := compact_test_gap f.val h0
  exact product_integrable _ _ (SourceLocalBounds.magnetic_locallyIntegrable (reclip d c hc) p i) f
    (fun x hx => (congrFun (magnetic_agrees d c hc p x (hs hx)) i).symm)

theorem partial_avoids_zero (f : Test) (h0 : (0 : Space)∉tsupport (f.val : Space → ℂ)) (i : Fin 3) :
    (0 : Space)∉tsupport ((testPartial i f).val : Space → ℂ) := by
  apply fun h => h0 (RegionalMaxwellHelmholtz.partial_tsupport f.val i h)

theorem pair_sub (E F : Field) (f : Test)
    (hE : ∀ i, Integrable (fun x => E x i*f.val x))
    (hF : ∀ i, Integrable (fun x => F x i*f.val x)) (i : Fin 3) :
    fieldPair (E-F) i f=fieldPair E i f-fieldPair F i f := by
  simp only [fieldPair,Pi.sub_apply,sub_mul]
  exact integral_sub (hE i) (hF i)

theorem curl_sub (E F : Field) (f : Test)
    (hE : ∀ i j, Integrable (fun x => E x i*(testPartial j f).val x))
    (hF : ∀ i j, Integrable (fun x => F x i*(testPartial j f).val x)) (i : Fin 3) :
    curlPair (fieldPair (E-F)) i f=curlPair (fieldPair E) i f-curlPair (fieldPair F) i f := by
  unfold curlPair
  rw [pair_sub E F _ (fun j => hE j _) (fun j => hF j _),
    pair_sub E F _ (fun j => hE j _) (fun j => hF j _)]
  ring

end OQ14.SourceTestIntegrals
#print axioms OQ14.SourceTestIntegrals.product_integrable
#print axioms OQ14.SourceTestIntegrals.electric_integrable
#print axioms OQ14.SourceTestIntegrals.magnetic_integrable
#print axioms OQ14.SourceTestIntegrals.partial_avoids_zero
#print axioms OQ14.SourceTestIntegrals.pair_sub
#print axioms OQ14.SourceTestIntegrals.curl_sub
