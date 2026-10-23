import SourceRegularCorrection
import SourceDielectricMaxwell
import TestFieldLocalization

/-! Literal origin-regularized TE source correction and its vacuum duality. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceTECorrection
open MeasureTheory Set OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
open OQ14.MaterialMaxwell OQ14.MagneticResponse OQ14.DynamicSource

def electric (d : Data) (p : HarmonicPolynomial.Poly) : Field := SourceRegularCorrection.magnetic d p
def magnetic (d : Data) (p : HarmonicPolynomial.Poly) : Field := -SourceRegularCorrection.electric d p
def polarization (d : Data) (p : HarmonicPolynomial.Poly) (i : Fin 3) (x : Space) : ℂ :=
  (SourceGeneralMaxwell.mu d ‖x‖-1)*SourceUnclippedMaxwell.magnetic d p x i

theorem electric_away (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) (hx : x≠0) :
    electric d p x=SourceGeneralMaxwell.teElectric d p x-SourceGeneralMaxwell.teElectric (vacuum d) p x :=
  SourceRegularCorrection.magnetic_away d p x hx

theorem magnetic_away (d : Data) (p : HarmonicPolynomial.Poly) (hp : p.IsHomogeneous d.l)
    (hh : HarmonicPolynomial.formalLaplacian p=0) (x : Space) (hx : x≠0) :
    magnetic d p x=SourceGeneralMaxwell.teMagnetic d p x-SourceGeneralMaxwell.teMagnetic (vacuum d) p x := by
  change -SourceRegularCorrection.electric d p x=_
  rw [SourceRegularCorrection.electric_away d p hp hh x hx]
  ext i
  simp only [SourceGeneralMaxwell.teMagnetic,Pi.neg_apply,Pi.sub_apply]
  ring

theorem polarization_inner (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) (hx : ‖x‖≤d.R) (i : Fin 3) :
    polarization d p i x=0 := by
  simp only [polarization,SourceGeneralMaxwell.mu,SourceRadialSystem.extend,if_pos hx,sub_self,zero_mul]

theorem polarization_outer (d : Data) (p : HarmonicPolynomial.Poly) (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    polarization d p i x=0 := by
  have hR := (RadialStack.chain_ordered d.chain).trans_lt hx
  simp only [polarization,SourceGeneralMaxwell.mu,SourceRadialSystem.extend,
    if_neg (not_le.mpr hR),if_neg (not_le.mpr hx),sub_self,zero_mul]

theorem vacuum_mu (d : Data) (r : ℝ) : SourceGeneralMaxwell.mu (vacuum d) r=1 :=
  SourceDielectricMaxwell.mu_one (vacuum d) (by simp [vacuum]) r

theorem fieldPair_neg (E : Field) (i : Fin 3) (f : Test) : fieldPair (-E) i f= -fieldPair E i f := by
  simp only [fieldPair,Pi.neg_apply,neg_mul,integral_neg]

theorem curlPair_neg (E : Field) (i : Fin 3) (f : Test) :
    curlPair (fieldPair (-E)) i f= -curlPair (fieldPair E) i f := by
  unfold curlPair
  rw [fieldPair_neg,fieldPair_neg]
  ring

theorem vacuum_dual (k : ℝ) (E H : Field) (h : TestMaxwell k (fun _ => 1) E H) :
    TestMaxwell k (fun _ => 1) H (-E) := by
  intro i f
  have he := (h i f).1
  have hh := (h i f).2
  simp only [Complex.ofReal_one,one_mul] at hh ⊢
  change curlPair (fieldPair H) i f= -(Complex.I*(k : ℂ))*fieldPair E i f at hh
  constructor
  · rw [fieldPair_neg,hh]; ring
  · change curlPair (fieldPair (-E)) i f= -(Complex.I*(k : ℂ))*fieldPair H i f
    rw [curlPair_neg,he]; ring

end OQ14.SourceTECorrection
#print axioms OQ14.SourceTECorrection.electric_away
#print axioms OQ14.SourceTECorrection.magnetic_away
#print axioms OQ14.SourceTECorrection.polarization_inner
#print axioms OQ14.SourceTECorrection.polarization_outer
#print axioms OQ14.SourceTECorrection.vacuum_mu
#print axioms OQ14.SourceTECorrection.fieldPair_neg
#print axioms OQ14.SourceTECorrection.curlPair_neg
#print axioms OQ14.SourceTECorrection.vacuum_dual
