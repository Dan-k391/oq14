import ScalarGreenInterior
import RadialSourceJump
import SphericalScalarWaves

/-! Actual matching and the exact source jump of the Green harmonic coefficients. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.ScalarGreenJump

open MeasureTheory Filter Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.RadialRellich
  OQ14.ScalarGreenMoment OQ14.ScalarGreenExterior OQ14.ScalarGreenInterior
  OQ14.SphericalMomentEquation OQ14.RadialMomentWeights
open scoped Topology

def innerProfile (l : ℕ) (k : ℂ) : ℝ → ℂ := RadialQuotient.profile 0 (RadialOriginSelection.regular l k)

def outerProfile (l : ℕ) (k : ℂ) : ℝ → ℂ := RadialQuotient.profile 0 (outgoing l k)

theorem quotient_residual (l : ℕ) (k : ℂ) (f df : ℝ → ℂ)
    (hf : ∀ r,0 < r → HasDerivAt f (df r) r)
    (hdf : ∀ r,0 < r → HasDerivAt df (radialCoefficient l k r*f r) r)
    (r : ℝ) (hr : 0 < r) :
    (r : ℂ)^2*deriv (deriv (RadialQuotient.profile 0 f)) r+
      2*(r : ℂ)*deriv (RadialQuotient.profile 0 f) r+
      (k^2*(r : ℂ)^2-(l : ℂ)*(l+1))*RadialQuotient.profile 0 f r=0 := by
  have hfirst := RadialQuotient.profile_hasDerivAt 0 f df r hr.ne' (hf r hr)
  have he : deriv (RadialQuotient.profile 0 f) =ᶠ[𝓝 r] RadialQuotient.profileD 0 f df := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with t ht
    exact (RadialQuotient.profile_hasDerivAt 0 f df t ht.ne' (hf t ht)).deriv
  have hsecond := (RadialQuotient.profileD_hasDerivAt 0 f df r hr.ne'
    (radialCoefficient l k r*f r) (hf r hr) (hdf r hr)).congr_of_eventuallyEq he
  rw [hsecond.deriv,hfirst.deriv]
  have hrc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  simp only [RadialQuotient.profileDD,RadialQuotient.profileD,RadialQuotient.profile,
    OQ14.RadialRellich.radialCoefficient,Nat.cast_zero,zero_add,one_mul,pow_one]
  field_simp [hrc]
  ring_nf
  field_simp [hrc]
  ring

theorem innerProfile_smooth (l : ℕ) (k : ℂ) (hk : k ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (innerProfile l k) (Ioi 0) :=
  SphericalScalarWaves.radialProfile_smooth 0 (RiccatiOriginSeries.origin l)
    (RiccatiOriginSeries.originD l) k hk (fun z _ => RiccatiOriginSeries.origin_hasDerivAt l z)

theorem outerProfile_smooth (l : ℕ) (k : ℂ) (hk : k ≠ 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (outerProfile l k) (Ioi 0) :=
  SphericalScalarWaves.radialProfile_smooth 0 (ModalAlgebra.xi l) (ModalAlgebra.xiD l)
    k hk (ModalAlgebra.xi_hasDerivAt l)

theorem innerProfile_residual (l : ℕ) (k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : 0 < r) :
    (r : ℂ)^2*deriv (deriv (innerProfile l k)) r+2*(r : ℂ)*deriv (innerProfile l k) r+
      (k^2*(r : ℂ)^2-(l : ℂ)*(l+1))*innerProfile l k r=0 :=
  quotient_residual l k (RadialOriginSelection.regular l k) (RadialOriginSelection.regularD l k)
    (fun t _ => RadialOriginSelection.regular_hasDerivAt l k t)
    (fun t ht => RadialOriginSelection.regularD_hasDerivAt l k hk t ht.ne') r hr

theorem outerProfile_residual (l : ℕ) (k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : 0 < r) :
    (r : ℂ)^2*deriv (deriv (outerProfile l k)) r+2*(r : ℂ)*deriv (outerProfile l k) r+
      (k^2*(r : ℂ)^2-(l : ℂ)*(l+1))*outerProfile l k r=0 :=
  quotient_residual l k (outgoing l k) (outgoingD l k)
    (fun t ht => outgoing_hasDerivAt l k hk t ht.ne')
    (fun t ht => outgoingD_hasDerivAt l k hk t ht.ne') r hr

theorem scaled_residual (l : ℕ) (k a : ℂ) (U : ℝ → ℂ) (r : ℝ)
    (hres : (r : ℂ)^2*deriv (deriv U) r+2*(r : ℂ)*deriv U r+
      (k^2*(r : ℂ)^2-(l : ℂ)*(l+1))*U r=0) :
    (r : ℂ)^2*deriv (deriv (fun t => a*U t)) r+2*(r : ℂ)*deriv (fun t => a*U t) r+
      (k^2*(r : ℂ)^2-(l : ℂ)*(l+1))*(a*U r)=0 := by
  simp only [deriv_const_mul_field']
  linear_combination a*hres

theorem source_matching (k : ℝ) (hk : 0 < k) (y : Space) (hy : y ≠ 0) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) :
    ∃ a b : ℂ,
      (∀ r ∈ Ioo 0 ‖y‖,coefficient k y p r=a*innerProfile l (k : ℂ) r) ∧
      (∀ r,‖y‖ < r → coefficient k y p r=b*outerProfile l (k : ℂ) r) ∧
      b*outerProfile l (k : ℂ) ‖y‖=a*innerProfile l (k : ℂ) ‖y‖ ∧
      (‖y‖ : ℂ)^(l+2)*(b*deriv (outerProfile l (k : ℂ)) ‖y‖-
        a*deriv (innerProfile l (k : ℂ)) ‖y‖)= -complexEvaluate p y := by
  obtain ⟨a,ha⟩ := regular_coefficient k hk.ne' y hy p l hp hh
  obtain ⟨b,hb,_⟩ := outgoing_coefficient k hk y p l hp hh
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  have hAm (r : ℝ) (hr : r ∈ Ioo 0 ‖y‖) : coefficient k y p r=a*innerProfile l (k : ℂ) r := by
    have h := ha r hr
    change (r : ℂ)*coefficient k y p r=a*RadialOriginSelection.regular l (k : ℂ) r at h
    unfold innerProfile RadialQuotient.profile
    rw [pow_one,← mul_div_assoc]
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr hr.1.ne')).mpr
    linear_combination h
  have hAp (r : ℝ) (hr : ‖y‖ < r) : coefficient k y p r=b*outerProfile l (k : ℂ) r := by
    have h := hb r hr
    unfold outerProfile RadialQuotient.profile
    rw [pow_one,← mul_div_assoc]
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr ((norm_nonneg y).trans_lt hr).ne')).mpr
    linear_combination h
  have hj := RadialSourceJump.radial_point_source_jump l (k : ℂ) ‖y‖ (norm_pos_iff.mpr hy)
    (complexEvaluate p y) (coefficient k y p)
    (fun r => a*innerProfile l (k : ℂ) r) (fun r => b*outerProfile l (k : ℂ) r)
    (contDiffOn_const.mul (innerProfile_smooth l (k : ℂ) hkc))
    (contDiffOn_const.mul (outerProfile_smooth l (k : ℂ) hkc))
    (fun r hr => scaled_residual l (k : ℂ) a _ r (innerProfile_residual l (k : ℂ) hkc r hr))
    (fun r hr => scaled_residual l (k : ℂ) b _ r (outerProfile_residual l (k : ℂ) hkc r hr)) hAm hAp
    (fun η hη hc hs => by
      simpa only [coefficientA,coefficientB,coefficientC,neg_mul,mul_neg,mul_comm] using
        weak_radial_polynomial_source k y p l hp hh η hη hc hs)
  refine ⟨a,b,hAm,hAp,hj.1,?_⟩
  simpa only [deriv_const_mul_field'] using hj.2

end OQ14.ScalarGreenJump

#print axioms OQ14.ScalarGreenJump.quotient_residual
#print axioms OQ14.ScalarGreenJump.innerProfile_smooth
#print axioms OQ14.ScalarGreenJump.outerProfile_smooth
#print axioms OQ14.ScalarGreenJump.innerProfile_residual
#print axioms OQ14.ScalarGreenJump.outerProfile_residual
#print axioms OQ14.ScalarGreenJump.scaled_residual
#print axioms OQ14.ScalarGreenJump.source_matching
