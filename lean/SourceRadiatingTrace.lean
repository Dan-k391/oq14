import RadiatingTrace
import SourceFarAmplitude
import SourceCoreReaction

/-! Genuine spherical outgoing traces of the literal layered source modes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceRadiatingTrace
open Complex Filter Set OQ14.Maxwell OQ14.SourceRadialSystem OQ14.HarmonicPolynomial
open OQ14.SourceRadiation OQ14.ModalAlgebra OQ14.AngularPower
open scoped Topology

def angularP (P : Poly) : C(Sphere,Vector) :=
  ⟨fun n => HarmonicRadiationFactors.poloidal P n,
    (HarmonicRadiationFactors.poloidal_continuous P).comp continuous_subtype_val⟩
def angularR (P : Poly) : C(Sphere,Vector) :=
  ⟨fun n => HarmonicRadiationFactors.radial P n,
    (HarmonicRadiationFactors.radial_continuous P).comp continuous_subtype_val⟩
def angularT (P : Poly) : C(Sphere,Vector) :=
  ⟨fun n => DebyeRadialTrace.angularToroidal P n,
    (HarmonicRadiationGeometry.angularToroidal_continuous P).comp continuous_subtype_val⟩

def electricMap (d : Data) (P : Poly) (r : ℝ) : C(Sphere,Vector) :=
  (amplitude d*phase d.l*(I*p d.l r+pD d.l r)) • angularP P+
    (amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l r/(r : ℂ))) • angularR P

def magneticMap (d : Data) (P : Poly) (r : ℝ) : C(Sphere,Vector) :=
  (-I*amplitude d*phase d.l*p d.l r) • angularT P

def electricFar (d : Data) (P : Poly) : C(Sphere,Vector) :=
  (amplitude d*phase d.l*I) • angularP P

def magneticFar (d : Data) (P : Poly) : C(Sphere,Vector) :=
  (-I*amplitude d*phase d.l) • angularT P

theorem electricMap_limit (d : Data) (P : Poly) :
    Tendsto (electricMap d P) atTop (𝓝 (electricFar d P)) := by
  have hpol : Tendsto (fun r : ℝ => p d.l r) atTop (𝓝 1) := by
    simpa only [one_mul] using RadialRellich.hankelPoly_radial_limit d.l 1 (by norm_num) I
  have hpd := HankelEnergy.hankelPolyD_tendsto d.l I
  have hpr : Tendsto (fun r : ℝ => p d.l r/(r : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using hpol.mul HankelEnergy.inverse_real_tendsto
  have h1 := (((hpol.const_mul I).add hpd).const_mul (amplitude d*phase d.l)).smul_const (angularP P)
  have h2 := (hpr.const_mul (amplitude d*phase d.l*((d.l : ℂ)*(d.l+1)))).smul_const (angularR P)
  have ht := h1.add h2
  convert ht using 1
  congr 1
  ext n i
  simp [electricFar,angularP,angularR,smul_eq_mul]
theorem magneticMap_limit (d : Data) (P : Poly) :
    Tendsto (magneticMap d P) atTop (𝓝 (magneticFar d P)) := by
  have hpol : Tendsto (fun r : ℝ => p d.l r) atTop (𝓝 1) := by
    simpa only [one_mul] using RadialRellich.hankelPoly_radial_limit d.l 1 (by norm_num) I
  simpa only [magneticMap,magneticFar,mul_one] using
    (hpol.const_mul (-I*amplitude d*phase d.l)).smul_const (angularT P)

theorem ray_weight (r : ℝ) (hr : 0<r) (n : Sphere) :
    MaxwellFarField.factor 1 r=Complex.exp (-I*(‖r • (n : Space)‖ : ℂ))*(‖r • (n : Space)‖ : ℂ) := by
  have hn : ‖r • (n : Space)‖=r := by
    simp only [norm_smul,sphere_norm,mul_one,Real.norm_eq_abs,abs_of_pos hr]
  rw [hn]
  simp only [MaxwellFarField.factor,Complex.ofReal_one,mul_one]
  ring

theorem electricMap_actual (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (r : ℝ) (hr : 0<r) (hX : d.X<r) (n : Sphere) :
    MaxwellFarField.factor 1 r • SourceUnclippedMaxwell.electric d P (r • (n : Space))=electricMap d P r n := by
  rw [ray_weight r hr n]
  exact SourceFarAmplitude.electric_ray d P hp n r hr hX

theorem magneticMap_actual (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l)
    (r : ℝ) (hr : 0<r) (hX : d.X<r) (n : Sphere) :
    MaxwellFarField.factor 1 r • SourceUnclippedMaxwell.magnetic d P (r • (n : Space))=magneticMap d P r n := by
  rw [ray_weight r hr n]
  exact SourceFarAmplitude.magnetic_ray d P hp n r hr hX

theorem position_direction (n : Sphere) : MaxwellRadiation.direction n=DebyeRadialTrace.position n := by
  ext i
  simp only [MaxwellRadiation.direction,GreenKernel.unitCoordinate,sphere_norm,Complex.ofReal_one,
    div_one,DebyeRadialTrace.position]

theorem toroidal_transverse (P : Poly) (n : Sphere) :
    dot (MaxwellRadiation.direction n) (DebyeRadialTrace.angularToroidal P n)=0 := by
  rw [position_direction]
  simp [dot,DebyeRadialTrace.position,DebyeRadialTrace.angularToroidal]
  ring

theorem poloidal_transverse (P : Poly) (n : Sphere) :
    dot (MaxwellRadiation.direction n) (HarmonicRadiationFactors.poloidal P n)=0 := by
  rw [position_direction]
  simp [dot,HarmonicRadiationFactors.poloidal,cross_apply,DebyeRadialTrace.position]
  ring

theorem cross_poloidal (P : Poly) (n : Sphere) :
    crossProduct (MaxwellRadiation.direction n) (HarmonicRadiationFactors.poloidal P n)=
      -DebyeRadialTrace.angularToroidal P n := by
  have hT := toroidal_transverse P n
  have hn := MaxwellRadiation.direction_dot (n : Space) (by
    intro he
    have hs := sphere_norm n
    rw [he,norm_zero] at hs
    norm_num at hs)
  rw [position_direction] at hT hn ⊢
  have ha (u v : Vector) : crossProduct u v= -crossProduct v u := by
    ext i
    fin_cases i <;> simp [cross_apply] <;> ring
  rw [HarmonicRadiationFactors.poloidal,ha]
  ext i
  rw [Pi.neg_apply,MaxwellRadiation.cross_cross_same,hn,hT]
  simp

theorem far_transverse (d : Data) (P : Poly) (n : Sphere) :
    dot (MaxwellRadiation.direction n) (electricFar d P n)=0 := by
  change dot _ ((amplitude d*phase d.l*I) • HarmonicRadiationFactors.poloidal P n)=0
  simp only [dot,Pi.smul_apply,smul_eq_mul]
  have ht := poloidal_transverse P n
  dsimp only [dot] at ht
  linear_combination (amplitude d*phase d.l*I)*ht

theorem far_cross (d : Data) (P : Poly) (n : Sphere) :
    crossProduct (MaxwellRadiation.direction n) (electricFar d P n)=magneticFar d P n := by
  change crossProduct _ ((amplitude d*phase d.l*I) • HarmonicRadiationFactors.poloidal P n)=_
  rw [map_smul,cross_poloidal]
  ext i
  simp only [electricFar,magneticFar,angularT,ContinuousMap.smul_apply,ContinuousMap.coe_mk,
    Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
  ring


theorem sphericalContinuous (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ∀ᶠ r : ℝ in atTop,Continuous (fun n : Sphere => SourceUnclippedMaxwell.electric d P (r • (n : Space))) ∧
      Continuous (fun n : Sphere => SourceUnclippedMaxwell.magnetic d P (r • (n : Space))) := by
  filter_upwards [eventually_gt_atTop (max d.X 0)] with r hr
  have hr0 : 0<r := (le_max_right _ _).trans_lt hr
  have hrX : d.X<r := (le_max_left _ _).trans_lt hr
  have hf : MaxwellFarField.factor 1 r≠0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hr0.ne') (Complex.exp_ne_zero _)
  have he : (fun n : Sphere => SourceUnclippedMaxwell.electric d P (r • (n : Space)))=
      fun n => (MaxwellFarField.factor 1 r)⁻¹ • electricMap d P r n := by
    funext n
    rw [←electricMap_actual d P hp r hr0 hrX n,smul_smul,inv_mul_cancel₀ hf,one_smul]
  have hh : (fun n : Sphere => SourceUnclippedMaxwell.magnetic d P (r • (n : Space)))=
      fun n => (MaxwellFarField.factor 1 r)⁻¹ • magneticMap d P r n := by
    funext n
    rw [←magneticMap_actual d P hp r hr0 hrX n,smul_smul,inv_mul_cancel₀ hf,one_smul]
  rw [he,hh]
  exact ⟨continuous_const.smul (electricMap d P r).continuous,
    continuous_const.smul (magneticMap d P r).continuous⟩

theorem uniform_bound (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ r : ℝ in atTop,∀ n : Sphere,∀ i : Fin 3,
      ‖MaxwellFarField.factor 1 r*SourceUnclippedMaxwell.electric d P (r • (n : Space)) i‖≤C ∧
      ‖MaxwellFarField.factor 1 r*SourceUnclippedMaxwell.magnetic d P (r • (n : Space)) i‖≤C := by
  refine ⟨‖electricFar d P‖+‖magneticFar d P‖+2,by positivity,?_⟩
  have he : ∀ᶠ r : ℝ in atTop,‖electricMap d P r‖<‖electricFar d P‖+1 :=
    (electricMap_limit d P).norm.eventually (gt_mem_nhds (by linarith))
  have hh : ∀ᶠ r : ℝ in atTop,‖magneticMap d P r‖<‖magneticFar d P‖+1 :=
    (magneticMap_limit d P).norm.eventually (gt_mem_nhds (by linarith))
  filter_upwards [he,hh,eventually_gt_atTop (max d.X 0)] with r hrE hrH hr n i
  have hr0 : 0<r := (le_max_right _ _).trans_lt hr
  have hrX : d.X<r := (le_max_left _ _).trans_lt hr
  have hE := congrFun (electricMap_actual d P hp r hr0 hrX n) i
  have hH := congrFun (magneticMap_actual d P hp r hr0 hrX n) i
  change MaxwellFarField.factor 1 r*SourceUnclippedMaxwell.electric d P (r • (n : Space)) i=electricMap d P r n i at hE
  change MaxwellFarField.factor 1 r*SourceUnclippedMaxwell.magnetic d P (r • (n : Space)) i=magneticMap d P r n i at hH
  rw [hE,hH]
  have hne := (norm_le_pi_norm (electricMap d P r n) i).trans ((electricMap d P r).norm_coe_le_norm n)
  have hnh := (norm_le_pi_norm (magneticMap d P r n) i).trans ((magneticMap d P r).norm_coe_le_norm n)
  constructor <;> linarith [norm_nonneg (electricFar d P),norm_nonneg (magneticFar d P)]

def tm_trace (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    RadiatingTrace.Trace 1 (SourceUnclippedMaxwell.electric d P) (SourceUnclippedMaxwell.magnetic d P) where
  far := electricFar d P
  transverse := far_transverse d P
  sphericalContinuous := sphericalContinuous d P hp
  bounded := uniform_bound d P hp
  electricLimit n := by
    have h := ((ContinuousMap.evalCLM ℂ n).continuous.tendsto (electricFar d P)).comp (electricMap_limit d P)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (max d.X 0)] with r hr
    exact (electricMap_actual d P hp r ((le_max_right _ _).trans_lt hr) ((le_max_left _ _).trans_lt hr) n).symm
  magneticLimit n := by
    rw [far_cross]
    have h := ((ContinuousMap.evalCLM ℂ n).continuous.tendsto (magneticFar d P)).comp (magneticMap_limit d P)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (max d.X 0)] with r hr
    exact (magneticMap_actual d P hp r ((le_max_right _ _).trans_lt hr) ((le_max_left _ _).trans_lt hr) n).symm

theorem cross_cross (n : Sphere) (A : Vector)
    (hA : dot (MaxwellRadiation.direction n) A=0) :
    crossProduct (MaxwellRadiation.direction n) (crossProduct (MaxwellRadiation.direction n) A)= -A := by
  have hn := MaxwellRadiation.direction_dot (n : Space) (by
    intro he
    have hs := sphere_norm n
    rw [he,norm_zero] at hs
    norm_num at hs)
  have ha (u v : Vector) : crossProduct u v= -crossProduct v u := by
    ext i
    fin_cases i <;> simp [cross_apply] <;> ring
  rw [ha]
  ext i
  rw [Pi.neg_apply,MaxwellRadiation.cross_cross_same,hn,hA]
  simp

def dual_trace {k : ℝ} {E H : Field} (t : RadiatingTrace.Trace k E H) :
    RadiatingTrace.Trace k H (-E) where
  far n := crossProduct (MaxwellRadiation.direction n) (t.far n)
  transverse n := by
    simp [dot,cross_apply]
    ring
  sphericalContinuous := by
    filter_upwards [t.sphericalContinuous] with r hr
    exact ⟨hr.2,hr.1.neg⟩
  bounded := by
    obtain ⟨C,hC,hb⟩ := t.bounded
    refine ⟨C,hC,?_⟩
    filter_upwards [hb] with r hr n i
    refine ⟨(hr n i).2,?_⟩
    simpa only [Pi.neg_apply,mul_neg,norm_neg] using (hr n i).1
  electricLimit := t.magneticLimit
  magneticLimit n := by
    rw [cross_cross n (t.far n) (t.transverse n)]
    simpa only [Pi.neg_apply,smul_neg] using (t.electricLimit n).neg

def te_trace (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    RadiatingTrace.Trace 1 (SourceGeneralMaxwell.teElectric d P) (SourceGeneralMaxwell.teMagnetic d P) :=
  dual_trace (tm_trace d P hp)

def tm_difference_trace (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    RadiatingTrace.Trace 1
      (SourceUnclippedMaxwell.electric d P-SourceUnclippedMaxwell.electric (SourceCoreReaction.vacuum d) P)
      (SourceUnclippedMaxwell.magnetic d P-SourceUnclippedMaxwell.magnetic (SourceCoreReaction.vacuum d) P) :=
  (tm_trace d P hp).sub (tm_trace (SourceCoreReaction.vacuum d) P hp)

def te_difference_trace (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    RadiatingTrace.Trace 1
      (SourceGeneralMaxwell.teElectric d P-SourceGeneralMaxwell.teElectric (SourceCoreReaction.vacuum d) P)
      (SourceGeneralMaxwell.teMagnetic d P-SourceGeneralMaxwell.teMagnetic (SourceCoreReaction.vacuum d) P) :=
  (te_trace d P hp).sub (te_trace (SourceCoreReaction.vacuum d) P hp)
end OQ14.SourceRadiatingTrace





#print axioms OQ14.SourceRadiatingTrace.electricMap_limit
#print axioms OQ14.SourceRadiatingTrace.magneticMap_limit
#print axioms OQ14.SourceRadiatingTrace.ray_weight
#print axioms OQ14.SourceRadiatingTrace.electricMap_actual
#print axioms OQ14.SourceRadiatingTrace.magneticMap_actual
#print axioms OQ14.SourceRadiatingTrace.position_direction
#print axioms OQ14.SourceRadiatingTrace.toroidal_transverse
#print axioms OQ14.SourceRadiatingTrace.poloidal_transverse
#print axioms OQ14.SourceRadiatingTrace.cross_poloidal
#print axioms OQ14.SourceRadiatingTrace.far_transverse
#print axioms OQ14.SourceRadiatingTrace.far_cross
#print axioms OQ14.SourceRadiatingTrace.sphericalContinuous
#print axioms OQ14.SourceRadiatingTrace.uniform_bound
#print axioms OQ14.SourceRadiatingTrace.cross_cross
#print axioms OQ14.SourceRadiatingTrace.tm_trace
#print axioms OQ14.SourceRadiatingTrace.dual_trace
#print axioms OQ14.SourceRadiatingTrace.te_trace
#print axioms OQ14.SourceRadiatingTrace.tm_difference_trace
#print axioms OQ14.SourceRadiatingTrace.te_difference_trace
