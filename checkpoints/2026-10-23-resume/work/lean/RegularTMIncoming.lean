import RegularTEMagneticTrace
import RegularTEDecomposition
import HarmonicRadiationFactors
import SolidMaxwellProfiles

/-! Actual TM Hankel parts and their incoming and outgoing sphere traces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace OQ14.RegularTMIncoming
open Complex Filter Set Metric OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.DebyeRadialTrace
open OQ14.RegularTEIncoming (radial radialD phase coefficient)
open scoped Topology
abbrev Sphere := SphereReactionKernel.Sphere

def electric (l : ℕ) (inward : Bool) (p : Poly) : Field :=
  I • RegularTEIncoming.magnetic l inward p
def magnetic (l : ℕ) (inward : Bool) (p : Poly) : Field :=
  (-I) • RegularTEIncoming.electric l inward p

def angularP (p : Poly) : C(Sphere,Vector) :=
  ⟨fun n => HarmonicRadiationFactors.poloidal p n,
    (HarmonicRadiationFactors.poloidal_continuous p).comp continuous_subtype_val⟩
def angularR (p : Poly) : C(Sphere,Vector) :=
  ⟨fun n => HarmonicRadiationFactors.radial p n,
    (HarmonicRadiationFactors.radial_continuous p).comp continuous_subtype_val⟩

theorem electric_split (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (x : Space) (hx : x≠0) :
    SolidMaxwellProfiles.electric l p x=electric l false p x+electric l true p x := by
  have h := congrArg (fun v : Vector => I • v) (RegularTEDecomposition.magnetic_split l p hp x hx)
  convert h using 1
  · ext i
    simp only [SolidMaxwellProfiles.electric,DebyeMaxwell.teMagnetic,DebyeMaxwell.tmElectric,
      Pi.smul_apply,smul_eq_mul,div_one]
    ring_nf
    simp only [I_sq]
    ring
  · ext i
    simp only [electric,Pi.smul_apply,Pi.add_apply,smul_eq_mul,mul_add]

theorem magnetic_split (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l) (x : Space) (hx : x≠0) :
    SolidMaxwellProfiles.magnetic l p x=magnetic l false p x+magnetic l true p x := by
  have h := congrArg (fun v : Vector => (-I) • v) (RegularTEDecomposition.electric_split l p hp x hx)
  convert h using 1
  · ext i
    simp only [SolidMaxwellProfiles.magnetic,DebyeMaxwell.tmMagnetic,DebyeMaxwell.teElectric,
      Pi.smul_apply,smul_eq_mul,mul_one]
  · ext i
    simp only [magnetic,Pi.smul_apply,Pi.add_apply,smul_eq_mul,mul_add]

theorem electric_ray (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (n : Sphere) (r : ℝ) (hr : 0<r) :
    electric l inward p (r • (n : Space))=
      (radialD l inward r/(2*(r : ℂ))) • HarmonicRadiationFactors.poloidal p n+
      ((l : ℂ)*(l+1)*radial l inward r/(2*(r : ℂ)^2)) • HarmonicRadiationFactors.radial p n := by
  have hn : ‖(n : Space)‖=1 := by simpa only [mem_sphere,dist_zero_right] using n.property
  have hdir : MaxwellRadiation.direction (n : Space)=position n := by
    ext i
    simp [MaxwellRadiation.direction,GreenKernel.unitCoordinate,hn,position]
  have hnn : dot (position n) (position n)=1 := by
    have h := MaxwellRadiation.direction_dot (n : Space) (norm_pos_iff.mp (by rw [hn]; norm_num))
    rwa [hdir] at h
  let H := RegularTEIncoming.magnetic l inward p (r • (n : Space))
  have hid (i : Fin 3) : H i=crossProduct (crossProduct (position n) H) (position n) i+
      dot (position n) H*position n i := by
    rw [MaxwellRadiation.cross_cross_same,hnn,one_mul]
    ring
  have hc := RegularTEIncoming.magnetic_tangent_ray l inward p hp hh n r hr
  have hd := RegularTEMagneticTrace.magnetic_radial_ray l inward p hp hh n r hr
  change crossProduct (position n) H=_ at hc
  change dot (position n) H=_ at hd
  ext i
  change I*H i=_
  rw [hid i,hc,hd]
  fin_cases i <;> simp [HarmonicRadiationFactors.poloidal,HarmonicRadiationFactors.radial,
    cross_apply,position,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
  all_goals ring_nf; simp only [I_sq]; ring

theorem magnetic_tangent_ray (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (n : Sphere) (r : ℝ) (hr : 0<r) :
    crossProduct (position n) (magnetic l inward p (r • (n : Space)))=
      (-I*radial l inward r/(2*(r : ℂ))) • HarmonicRadiationFactors.poloidal p n := by
  rw [magnetic]
  change crossProduct (position n) ((-I) • RegularTEIncoming.electric l inward p (r • (n : Space)))=_
  rw [map_smul,RegularTEIncoming.electric_ray l inward p hp n r hr,map_smul,smul_smul]
  congr 1
  ring

def electricMap (l : ℕ) (inward : Bool) (p : Poly) (r : ℝ) : C(Sphere,Vector) :=
  (phase inward r*radialD l inward r/2) • angularP p+
    ((l : ℂ)*(l+1)*(phase inward r*radial l inward r/(r : ℂ))/2) • angularR p

def magneticTangentMap (l : ℕ) (inward : Bool) (p : Poly) (r : ℝ) : C(Sphere,Vector) :=
  (-I*(phase inward r*radial l inward r)/2) • angularP p

theorem electricMap_actual (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (hh : formalLaplacian p=0) (r : ℝ) (hr : 0<r) (n : Sphere) :
    (phase inward r*(r : ℂ)) • electric l inward p (r • (n : Space))=electricMap l inward p r n := by
  rw [electric_ray l inward p hp hh n r hr]
  ext i
  simp only [electricMap,angularP,angularR,ContinuousMap.add_apply,ContinuousMap.smul_apply,
    ContinuousMap.coe_mk,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  field_simp [hrc]
  ring

theorem magneticTangentMap_actual (l : ℕ) (inward : Bool) (p : Poly) (hp : p.IsHomogeneous l)
    (r : ℝ) (hr : 0<r) (n : Sphere) :
    (phase inward r*(r : ℂ)) • crossProduct (position n) (magnetic l inward p (r • (n : Space)))=
      magneticTangentMap l inward p r n := by
  rw [magnetic_tangent_ray l inward p hp n r hr]
  ext i
  simp only [magneticTangentMap,angularP,ContinuousMap.smul_apply,ContinuousMap.coe_mk,
    Pi.smul_apply,smul_eq_mul]
  have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
  field_simp [hrc]
  ring

theorem electricMap_limit (l : ℕ) (inward : Bool) (p : Poly) :
    Tendsto (electricMap l inward p) atTop
      (𝓝 ((coefficient l inward*(if inward then -I else I)/2) • angularP p)) := by
  have hr : Tendsto (fun r : ℝ => phase inward r*radial l inward r/(r : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (RegularTEIncoming.scaled_radial_limit l inward).mul HankelEnergy.inverse_real_tendsto
  have h1 := ((RegularTEIncoming.scaled_radialD_limit l inward).div_const (2 : ℂ)).smul_const (angularP p)
  have h2 := ((hr.const_mul ((l : ℂ)*(l+1))).div_const (2 : ℂ)).smul_const (angularR p)
  have h := h1.add h2
  convert h using 1
  congr 1
  ext n i
  simp [angularP,angularR,smul_eq_mul]

theorem magneticTangentMap_limit (l : ℕ) (inward : Bool) (p : Poly) :
    Tendsto (magneticTangentMap l inward p) atTop
      (𝓝 ((-I*coefficient l inward/2) • angularP p)) :=
  (((RegularTEIncoming.scaled_radial_limit l inward).const_mul (-I)).div_const (2 : ℂ)).smul_const (angularP p)

end OQ14.RegularTMIncoming
#print axioms OQ14.RegularTMIncoming.electric_split
#print axioms OQ14.RegularTMIncoming.magnetic_split
#print axioms OQ14.RegularTMIncoming.electric_ray
#print axioms OQ14.RegularTMIncoming.magnetic_tangent_ray
#print axioms OQ14.RegularTMIncoming.electricMap_actual
#print axioms OQ14.RegularTMIncoming.magneticTangentMap_actual
#print axioms OQ14.RegularTMIncoming.electricMap_limit
#print axioms OQ14.RegularTMIncoming.magneticTangentMap_limit
