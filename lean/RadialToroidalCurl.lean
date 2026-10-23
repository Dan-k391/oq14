import LayerMagneticProfiles

/-! A first-derivative formula for an arbitrary radial toroidal multiplier. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.RadialToroidalCurl
open Set Filter OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.DebyeRadialTrace
  OQ14.RadialMultiplierWeak OQ14.ExteriorClassical OQ14.DebyeCalculus
open scoped Topology

theorem curl_formula (a : ℝ → ℂ) (aD : ℂ) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (x : Space) (hx : x≠0) (ha : HasDerivAt a aD ‖x‖) (i : Fin 3) :
    curl (field a (angularToroidal p)) x i=
      ((‖x‖ : ℂ)*aD+(l+1 : ℂ)*a ‖x‖)*dcoord (complexEvaluate p) x i-
        (l : ℂ)*aD/(‖x‖ : ℂ)*(x i : ℂ)*complexEvaluate p x := by
  let η : ℝ → ℂ := fun t => a ‖x‖+((t : ℂ)-(‖x‖ : ℂ))*aD
  have hη : ContDiff ℝ (⊤ : ℕ∞) η :=
    contDiff_const.add ((Complex.ofRealCLM.contDiff.sub contDiff_const).mul contDiff_const)
  have hηD : HasDerivAt η aD ‖x‖ := by
    convert (((Complex.ofRealCLM.hasDerivAt).sub_const (‖x‖ : ℂ)).mul_const aD).const_add (a ‖x‖) using 1
    simp
  have hη0 : η ‖x‖=a ‖x‖ := by simp [η]
  have hpd (j k : Fin 3) : pd (field a (angularToroidal p)) x j k=
      pd (field η (angularToroidal p)) x j k := by
    rw [field_partial a _ x hx aD ha (fun j => (LayerMagneticProfiles.angular_smooth p j).differentiable (by simp) x),
      field_partial η _ x hx aD hηD (fun j => (LayerMagneticProfiles.angular_smooth p j).differentiable (by simp) x),hη0]
  have hc : curl (field a (angularToroidal p)) x=curl (field η (angularToroidal p)) x := by
    ext j
    fin_cases j <;> simp only [curl,hpd]
  have he : field η (angularToroidal p) =ᶠ[𝓝 x] toroidal (scalar η p) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    ext j
    exact (toroidal_components η hη.contDiffOn p y hy j).symm
  rw [hc,curl_congr_nhds he,toroidal_curl η hη.contDiffOn p l hp hh x hx i,hηD.deriv,hη0]

end OQ14.RadialToroidalCurl

#print axioms OQ14.RadialToroidalCurl.curl_formula
