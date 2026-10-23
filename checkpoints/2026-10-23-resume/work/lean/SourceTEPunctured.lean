import SourceTECorrection
import SourceTestIntegrals

/-! Actual TE polarization equations through all material interfaces on punctured space. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.SourceTEPunctured
open MeasureTheory Set OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.MaterialMaxwell OQ14.MagneticResponse OQ14.DynamicSource

theorem magnetic_integrable (d : Data) (p : HarmonicPolynomial.Poly) (f : Test)
    (h0 : (0 : Space)∉tsupport (f.val : Space → ℂ)) (i : Fin 3) :
    Integrable (fun x => SourceGeneralMaxwell.teMagnetic d p x i*f.val x) := by
  simpa only [SourceGeneralMaxwell.teMagnetic,neg_mul] using
    (SourceTestIntegrals.electric_integrable d p f h0 i).neg

theorem equation (d : Data) (hσ : ∀ g∈d.gs,g.σ=1)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0)
    (hρ : ∀ i, Integrable (SourceTECorrection.polarization d p i)) (f : Test)
    (h0 : (0 : Space)∉tsupport (f.val : Space → ℂ)) :
    ForcedTestLocalization.Equation 1 (SourceTECorrection.polarization d p)
      (SourceTECorrection.electric d p) (SourceTECorrection.magnetic d p) f := by
  let E := SourceGeneralMaxwell.teElectric d p
  let H := SourceGeneralMaxwell.teMagnetic d p
  let V := SourceGeneralMaxwell.teElectric (vacuum d) p
  let W := SourceGeneralMaxwell.teMagnetic (vacuum d) p
  let ρ := SourceTECorrection.polarization d p
  have hE := SourceTestIntegrals.magnetic_integrable d p f h0
  have hH := magnetic_integrable d p f h0
  have hV := SourceTestIntegrals.magnetic_integrable (vacuum d) p f h0
  have hW := magnetic_integrable (vacuum d) p f h0
  have hEp (i j : Fin 3) := SourceTestIntegrals.magnetic_integrable d p (testPartial j f)
    (SourceTestIntegrals.partial_avoids_zero f h0 j) i
  have hHp (i j : Fin 3) := magnetic_integrable d p (testPartial j f)
    (SourceTestIntegrals.partial_avoids_zero f h0 j) i
  have hVp (i j : Fin 3) := SourceTestIntegrals.magnetic_integrable (vacuum d) p (testPartial j f)
    (SourceTestIntegrals.partial_avoids_zero f h0 j) i
  have hWp (i j : Fin 3) := magnetic_integrable (vacuum d) p (testPartial j f)
    (SourceTestIntegrals.partial_avoids_zero f h0 j) i
  have hfirst (a : Data) (ha : ∀ g∈a.gs,g.σ=1) (hpa : p.IsHomogeneous a.l) (i : Fin 3) :
      curlPair (fieldPair (SourceGeneralMaxwell.teElectric a p)) i f=
        Complex.I*fieldPair (SourceGeneralMaxwell.teMagnetic a p) i f := by
    have h := congrFun (SourceDielectricMaxwell.te_dielectric_weak a ha p hpa hh f.val
      (f.val.smooth 2) f.property h0).1 i
    rw [TestFieldLocalization.weak_pair_eq] at h
    simpa only [fieldPair,mul_assoc,integral_const_mul] using h
  have hsecond (a : Data) (i : Fin 3) :
      curlPair (fieldPair (SourceGeneralMaxwell.teMagnetic a p)) i f=
        -Complex.I*(∫ x,SourceGeneralMaxwell.mu a ‖x‖*SourceGeneralMaxwell.teElectric a p x i*f.val x) := by
    have h := congrFun (SourceGeneralMaxwell.te_second_weak_maxwell a p f.val (f.val.smooth 2) f.property h0) i
    rw [TestFieldLocalization.weak_pair_eq] at h
    simpa only [mul_assoc,integral_const_mul] using h
  have hpair (i : Fin 3) : (∫ x,SourceGeneralMaxwell.mu d ‖x‖*E x i*f.val x)=
      fieldPair E i f+∫ x,ρ i x*f.val x := by
    have he : (fun x => SourceGeneralMaxwell.mu d ‖x‖*E x i*f.val x)=
        fun x => E x i*f.val x+ρ i x*f.val x := by
      funext x
      dsimp [ρ,E,SourceTECorrection.polarization,SourceGeneralMaxwell.teElectric]
      ring
    rw [he]
    exact integral_add (hE i)
      (PointSingularity.test_product_integrable _ _ (hρ i).locallyIntegrable f.val.continuous f.property)
  have hvsecond (i : Fin 3) : curlPair (fieldPair W) i f= -Complex.I*fieldPair V i f := by
    simpa only [SourceTECorrection.vacuum_mu,one_mul,fieldPair] using hsecond (vacuum d) i
  have hraw : ForcedTestLocalization.Equation 1 ρ (E-V) (H-W) f := by
    intro i
    simp only [Complex.ofReal_one,mul_one]
    constructor
    · rw [SourceTestIntegrals.curl_sub E V f hEp hVp i,
        SourceTestIntegrals.pair_sub H W f hH hW i,hfirst d hσ hp i,
        hfirst (vacuum d) (by simp [vacuum]) hp i]
      ring
    · rw [SourceTestIntegrals.curl_sub H W f hHp hWp i,
        SourceTestIntegrals.pair_sub E V f hE hV i,hsecond d i,hvsecond i,hpair i]
      ring
  apply TestFieldLocalization.equation_congr 1 ρ ρ (E-V) (H-W) _ _ f _ _ (fun _ _ _ => rfl) hraw
  · intro x hx
    exact (SourceTECorrection.electric_away d p x (by intro hz; subst x; exact h0 hx)).symm
  · intro x hx
    exact (SourceTECorrection.magnetic_away d p hp hh x (by intro hz; subst x; exact h0 hx)).symm

end OQ14.SourceTEPunctured
#print axioms OQ14.SourceTEPunctured.magnetic_integrable
#print axioms OQ14.SourceTEPunctured.equation
