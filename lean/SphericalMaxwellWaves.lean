import SphericalScalarWaves
import SolidScalarHelmholtz

/-! Genuine all-degree Maxwell waves from actual regular and outgoing radial functions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.SphericalMaxwellWaves
open OQ14.Maxwell OQ14.ModalDipole OQ14.DebyeMaxwell OQ14.HarmonicPolynomial
  OQ14.ModalAlgebra OQ14.ModalWronskian

theorem regular_te (l : ℕ) (q k ε : ℂ) (hk : k ≠ 0) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) :
    ComplexMaxwellAt k ε (teElectric (SolidScalarHelmholtz.wave l q p))
      (teMagnetic k (SolidScalarHelmholtz.wave l q p)) x :=
  te_maxwell isOpen_univ _ (fun _ _ => (SolidScalarHelmholtz.wave_contDiff l q p).contDiffAt)
    q k ε hk hdisp (fun y _ => SolidScalarHelmholtz.wave_helmholtz l q p hp hh y) x (Set.mem_univ x)

theorem regular_tm (l : ℕ) (q k ε : ℂ) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) :
    ComplexMaxwellAt k ε (tmElectric (SolidScalarHelmholtz.wave l q p))
      (tmMagnetic k ε (SolidScalarHelmholtz.wave l q p)) x :=
  tm_maxwell isOpen_univ _ (fun _ _ => (SolidScalarHelmholtz.wave_contDiff l q p).contDiffAt)
    q k ε hdisp (fun y _ => SolidScalarHelmholtz.wave_helmholtz l q p hp hh y) x (Set.mem_univ x)

theorem outgoing_te (l : ℕ) (q k ε : ℂ) (hq : q ≠ 0) (hk : k ≠ 0) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    ComplexMaxwellAt k ε (teElectric (SphericalScalarWaves.scalar l (xi l) q p))
      (teMagnetic k (SphericalScalarWaves.scalar l (xi l) q p)) x :=
  te_maxwell isOpen_compl_singleton _
    (fun y hy => SphericalScalarWaves.scalar_smooth l (xi l) (xiD l) q hq (xi_hasDerivAt l) p y hy)
    q k ε hk hdisp (fun y hy => SphericalScalarWaves.outgoing_helmholtz l q hq p hp hh y hy) x hx

theorem outgoing_tm (l : ℕ) (q k ε : ℂ) (hq : q ≠ 0) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    ComplexMaxwellAt k ε (tmElectric (SphericalScalarWaves.scalar l (xi l) q p))
      (tmMagnetic k ε (SphericalScalarWaves.scalar l (xi l) q p)) x :=
  tm_maxwell isOpen_compl_singleton _
    (fun y hy => SphericalScalarWaves.scalar_smooth l (xi l) (xiD l) q hq (xi_hasDerivAt l) p y hy)
    q k ε hdisp (fun y hy => SphericalScalarWaves.outgoing_helmholtz l q hq p hp hh y hy) x hx

theorem regular_te_real (l : ℕ) (q k ε : ℝ) (hk : k ≠ 0) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) :
    MaxwellAt k 1 ε (teElectric (SolidScalarHelmholtz.wave l q p))
      (teMagnetic k (SolidScalarHelmholtz.wave l q p)) x := by
  have hd : (q : ℂ)^2=(k : ℂ)^2*(ε : ℂ) := by exact_mod_cast hdisp
  simpa only [MaxwellAt,ComplexMaxwellAt,Complex.ofReal_one,mul_one] using
    regular_te l q k ε (Complex.ofReal_ne_zero.mpr hk) hd p hp hh x

theorem regular_tm_real (l : ℕ) (q k ε : ℝ) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) :
    MaxwellAt k 1 ε (tmElectric (SolidScalarHelmholtz.wave l q p))
      (tmMagnetic k ε (SolidScalarHelmholtz.wave l q p)) x := by
  have hd : (q : ℂ)^2=(k : ℂ)^2*(ε : ℂ) := by exact_mod_cast hdisp
  simpa only [MaxwellAt,ComplexMaxwellAt,Complex.ofReal_one,mul_one] using
    regular_tm l q k ε hd p hp hh x

theorem outgoing_te_real (l : ℕ) (q k ε : ℝ) (hq : q ≠ 0) (hk : k ≠ 0) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    MaxwellAt k 1 ε (teElectric (SphericalScalarWaves.scalar l (xi l) q p))
      (teMagnetic k (SphericalScalarWaves.scalar l (xi l) q p)) x := by
  have hd : (q : ℂ)^2=(k : ℂ)^2*(ε : ℂ) := by exact_mod_cast hdisp
  simpa only [MaxwellAt,ComplexMaxwellAt,Complex.ofReal_one,mul_one] using
    outgoing_te l q k ε (Complex.ofReal_ne_zero.mpr hq) (Complex.ofReal_ne_zero.mpr hk) hd p hp hh x hx

theorem outgoing_tm_real (l : ℕ) (q k ε : ℝ) (hq : q ≠ 0) (hdisp : q^2=k^2*ε)
    (p : Poly) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0) (x : Space) (hx : x ≠ 0) :
    MaxwellAt k 1 ε (tmElectric (SphericalScalarWaves.scalar l (xi l) q p))
      (tmMagnetic k ε (SphericalScalarWaves.scalar l (xi l) q p)) x := by
  have hd : (q : ℂ)^2=(k : ℂ)^2*(ε : ℂ) := by exact_mod_cast hdisp
  simpa only [MaxwellAt,ComplexMaxwellAt,Complex.ofReal_one,mul_one] using
    outgoing_tm l q k ε (Complex.ofReal_ne_zero.mpr hq) hd p hp hh x hx

end OQ14.SphericalMaxwellWaves

#print axioms OQ14.SphericalMaxwellWaves.regular_te
#print axioms OQ14.SphericalMaxwellWaves.regular_tm
#print axioms OQ14.SphericalMaxwellWaves.outgoing_te
#print axioms OQ14.SphericalMaxwellWaves.outgoing_tm
#print axioms OQ14.SphericalMaxwellWaves.regular_te_real
#print axioms OQ14.SphericalMaxwellWaves.regular_tm_real
#print axioms OQ14.SphericalMaxwellWaves.outgoing_te_real
#print axioms OQ14.SphericalMaxwellWaves.outgoing_tm_real
