import SourceTestIntegrals
import SourceRegularNear

/-! The actual polarization-driven Maxwell equations through every layer away from the origin. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.SourcePuncturedCorrection
open MeasureTheory Set OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.MaterialMaxwell OQ14.MagneticResponse OQ14.DynamicSource

theorem polarization_integrable (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    Integrable (SourceRegularCorrection.polarization d p i) := by
  exact SourceLocalBounds.source_integrable (SourceUnclippedMaxwell.reclip d (d.R/4) (by linarith [d.hR]))
    (by change d.R/4<d.R; linarith [d.hR]) p i

theorem equation (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (f : Test)
    (h0 : (0 : Space)∉tsupport (f.val : Space → ℂ)) :
    ForcedTestLocalization.Equation 1 (SourceRegularCorrection.polarization d p)
      (SourceRegularCorrection.electric d p) (SourceRegularCorrection.magnetic d p) f := by
  let E := SourceUnclippedMaxwell.electric d p
  let H := SourceUnclippedMaxwell.magnetic d p
  let V := SourceUnclippedMaxwell.electric (vacuum d) p
  let W := SourceUnclippedMaxwell.magnetic (vacuum d) p
  let ρ := SourceRegularCorrection.polarization d p
  have hE := SourceTestIntegrals.electric_integrable d p f h0
  have hH := SourceTestIntegrals.magnetic_integrable d p f h0
  have hV := SourceTestIntegrals.electric_integrable (vacuum d) p f h0
  have hW := SourceTestIntegrals.magnetic_integrable (vacuum d) p f h0
  have hEp (i j : Fin 3) := SourceTestIntegrals.electric_integrable d p (testPartial j f)
    (SourceTestIntegrals.partial_avoids_zero f h0 j) i
  have hHp (i j : Fin 3) := SourceTestIntegrals.magnetic_integrable d p (testPartial j f)
    (SourceTestIntegrals.partial_avoids_zero f h0 j) i
  have hVp (i j : Fin 3) := SourceTestIntegrals.electric_integrable (vacuum d) p (testPartial j f)
    (SourceTestIntegrals.partial_avoids_zero f h0 j) i
  have hWp (i j : Fin 3) := SourceTestIntegrals.magnetic_integrable (vacuum d) p (testPartial j f)
    (SourceTestIntegrals.partial_avoids_zero f h0 j) i
  have hfirst (a : Data) (ha : ∀ g∈a.gs,g.q^2=g.σ) (i : Fin 3) :
      curlPair (fieldPair (SourceUnclippedMaxwell.electric a p)) i f=
        Complex.I*fieldPair (SourceUnclippedMaxwell.magnetic a p) i f := by
    have h := congrFun (SourceUnclippedMaxwell.first_weak_maxwell a ha p f.val (f.val.smooth 2) f.property h0) i
    rw [TestFieldLocalization.weak_pair_eq] at h
    simpa only [fieldPair,mul_assoc,integral_const_mul] using h
  have hsecond (a : Data) (ha : p.IsHomogeneous a.l) (i : Fin 3) :
      curlPair (fieldPair (SourceUnclippedMaxwell.magnetic a p)) i f=
        -Complex.I*(∫ x,sigma a ‖x‖*SourceUnclippedMaxwell.electric a p x i*f.val x) := by
    have h := congrFun (SourceUnclippedMaxwell.second_weak_maxwell a p ha hh f.val (f.val.smooth 1) f.property h0) i
    rw [TestFieldLocalization.weak_pair_eq] at h
    simpa only [mul_assoc,integral_const_mul] using h
  have hpair (i : Fin 3) : (∫ x,sigma d ‖x‖*E x i*f.val x)=
      fieldPair E i f+∫ x,ρ i x*f.val x := by
    have he : (fun x => sigma d ‖x‖*E x i*f.val x)=
        fun x => E x i*f.val x+ρ i x*f.val x := by
      funext x
      dsimp [ρ,E,SourceRegularCorrection.polarization]
      ring
    rw [he,integral_add (hE i)
      (PointSingularity.test_product_integrable _ _ (polarization_integrable d p i).locallyIntegrable f.val.continuous f.property)]
    rfl
  have hvsecond (i : Fin 3) : curlPair (fieldPair W) i f= -Complex.I*fieldPair V i f := by
    simpa only [SourceRegularCorrection.vacuum_sigma,one_mul,fieldPair] using hsecond (vacuum d) hp i
  have hraw : ForcedTestLocalization.Equation 1 ρ (E-V) (H-W) f := by
    intro i
    simp only [Complex.ofReal_one,mul_one]
    constructor
    · rw [SourceTestIntegrals.curl_sub E V f hEp hVp i,
        SourceTestIntegrals.pair_sub H W f hH hW i,hfirst d hdisp i,
        hfirst (vacuum d) (by simp [vacuum]) i]
      ring
    · rw [SourceTestIntegrals.curl_sub H W f hHp hWp i,
        SourceTestIntegrals.pair_sub E V f hE hV i,hsecond d hp i,hvsecond i,hpair i]
      ring
  apply TestFieldLocalization.equation_congr 1 ρ ρ (E-V) (H-W) _ _ f _ _ (fun _ _ _ => rfl) hraw
  · intro x hx
    exact (SourceRegularCorrection.electric_away d p hp hh x (by intro hz; subst x; exact h0 hx)).symm
  · intro x hx
    exact (SourceRegularCorrection.magnetic_away d p x (by intro hz; subst x; exact h0 hx)).symm

end OQ14.SourcePuncturedCorrection
#print axioms OQ14.SourcePuncturedCorrection.polarization_integrable
#print axioms OQ14.SourcePuncturedCorrection.equation
