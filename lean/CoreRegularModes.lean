import CoreFreePotential
import CoreReactionDegree
import SourceModeReaction

/-! The regular Maxwell modes in the core: the weak Maxwell equations of the polarized regular pairs
(`solidE`, `solidH`), their plane decomposition against a degree-uniform multiplier bound, and the
degree-summable constants. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CoreRegularModes
open MeasureTheory Filter Set Metric Complex OQ14.Maxwell OQ14.SourceRemotePlaneBand OQ14.CoreWeakSeries
  OQ14.CoreWeakLinear OQ14.CoreOutgoingModes OQ14.CoreFreePotential OQ14.BackgroundModeMaxwell
  OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
  OQ14.AngularExteriorBounds OQ14.HankelRealBasis
open OQ14.BarrierDegreeFluxConstants (decomp_mono)
open scoped Topology ComplexConjugate

/-! ### Summability over the positive index -/

theorem poly_geom_summable (k : ℕ) :
    Summable (fun a : PositiveIndex => ((a.1 : ℝ)+2)^k * (1/2 : ℝ)^(a.1+1)) := by
  apply (summable_sigma_of_nonneg (fun _ => by positivity)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simp only [tsum_fintype]
  have hs : Summable (fun n : ℕ => (n+2 : ℝ)^(k+3)*(1/2 : ℝ)^(n+1)) := by
    have h := (RadialHighOrderTail.polynomial_geometric_summable (k+3)).comp_injective Nat.succ_injective
    simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_assoc,
      show (1 : ℝ)+1=2 by norm_num] using h
  apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => by positivity)) _ hs
  intro n
  have hcard : (Fintype.card (Index (n+1)) : ℝ) ≤ (n+2 : ℝ)^3 := by
    simpa only [Index,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one,add_assoc,
      show (1 : ℝ)+1=2 by norm_num] using
      (Nat.cast_le (α := ℝ)).mpr (SphereHarmonicDimension.harmonicSpace_finrank_le (n+1))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc (Fintype.card (Index (n+1)) : ℝ) * (((n : ℝ)+2)^k * (1/2 : ℝ)^(n+1))
      ≤ (n+2 : ℝ)^3 * (((n : ℝ)+2)^k * (1/2 : ℝ)^(n+1)) := by gcongr
    _ = (n+2 : ℝ)^(k+3)*(1/2 : ℝ)^(n+1) := by ring

/-! ### The weak Maxwell equations of the regular pairs -/

theorem testMaxwell_solid (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (hh : formalLaplacian P = 0) :
    MaterialMaxwell.TestMaxwell 1 (fun _ => 1) (SolidMaxwellProfiles.electric l P)
      (SolidMaxwellProfiles.magnetic l P) :=
  MaterialMaxwell.classical_vacuum_testMaxwell 1 _ _
    (fun i => (SolidMaxwellProfiles.electric_smooth l P i).of_le (by simp))
    (fun i => (SolidMaxwellProfiles.magnetic_smooth l P i).of_le (by simp))
    (SolidMaxwellProfiles.actual_maxwell l P hp hh)

theorem weak_solid_tm (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (hh : formalLaplacian P = 0)
    (Ω : Set Space) :
    WeakOn Ω (SolidMaxwellProfiles.electric l P) (SolidMaxwellProfiles.magnetic l P) := by
  intro i f _
  have h := (testMaxwell_solid l P hp hh i f).1
  simpa using h

theorem weak_solid_te (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (hh : formalLaplacian P = 0)
    (Ω : Set Space) :
    WeakOn Ω (SolidMaxwellProfiles.magnetic l P) (fun x i => -SolidMaxwellProfiles.electric l P x i) := by
  intro i f _
  have h := (testMaxwell_solid l P hp hh i f).2
  rw [fieldPair_neg]
  have e : (∫ x, ((1 : ℝ) : ℂ) * SolidMaxwellProfiles.electric l P x i * f.val x) =
      MaterialMaxwell.fieldPair (SolidMaxwellProfiles.electric l P) i f := by
    unfold MaterialMaxwell.fieldPair
    simp
  rw [e] at h
  rw [h]
  simp

theorem weak_solid_pair (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (hh : formalLaplacian P = 0)
    (Ω : Set Space) (α β : ℂ) :
    WeakOn Ω (fun x i => α * SolidMaxwellProfiles.electric l P x i + β * SolidMaxwellProfiles.magnetic l P x i)
      (fun x i => α * SolidMaxwellProfiles.magnetic l P x i - β * SolidMaxwellProfiles.electric l P x i) :=
  weakOn_combo _ _ α β
    (fun j => (SolidMaxwellProfiles.electric_smooth l P j).continuous.continuousOn)
    (fun j => (SolidMaxwellProfiles.magnetic_smooth l P j).continuous.continuousOn)
    (weak_solid_tm l P hp hh Ω) (weak_solid_te l P hp hh Ω)

/-! ### Plane decomposition of the regular modes -/

/-- The degree majorant of the shell reaction: the mass bound, the coefficient scales and the geometric
degree decay of the reaction multiplier. -/
def regConst (b m C : ℝ) (a : PositiveIndex) : ℝ :=
  m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * C * ((a.1 : ℝ)+2)^9 * (1/2 : ℝ)^(a.1+1)

theorem regConst_nonneg (b m C : ℝ) (hb : 0 ≤ b) (hm : 0 ≤ m) (hC : 0 ≤ C) (a : PositiveIndex) :
    0 ≤ regConst b m C a := by
  have h0 := DebyeJetBounds.scale_nonnegative 0 b hb
  have h1 : 0 ≤ AngularExteriorBounds.scale := by
    dsimp [AngularExteriorBounds.scale, HarmonicSpatialMajorant.areaScale]
    positivity
  unfold regConst
  positivity

theorem regConst_summable (b m C : ℝ) : Summable (regConst b m C) := by
  have h := (poly_geom_summable 9).mul_left (m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * C)
  refine h.congr fun a => ?_
  unfold regConst
  ring

theorem envelope_eq (a : PositiveIndex) :
    envelope (a.1+1) = AngularExteriorBounds.scale * ((a.1 : ℝ)+2)^3 * AngularExteriorBounds.base^(a.1+1) := by
  unfold AngularExteriorBounds.envelope
  push_cast
  ring

theorem regular_piece (b B m C mu : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hm : 0 ≤ m) (hC : 0 ≤ C) (hmu : 0 ≤ mu)
    (a : PositiveIndex) (c : ℂ) (hc : ‖c‖ ≤ m * coefBound b B a * mu) (x : Space) (hx0 : x ≠ 0)
    (hΘ : RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) * mu *
        (|regular (a.1+1) ‖x‖| + |regularD (a.1+1) ‖x‖|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1)) :
    Decomp (regConst b m C a) (regConst b m C a)
      (c • fun i => SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) x ∧
    Decomp (2 * regConst b m C a) 0
      (c • fun i => SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) x := by
  have hscale0 := DebyeJetBounds.scale_nonnegative 0 b hb
  have hscaleA : 0 ≤ AngularExteriorBounds.scale := by
    dsimp [AngularExteriorBounds.scale, HarmonicSpatialMajorant.areaScale]
    positivity
  have hbase : 0 ≤ AngularExteriorBounds.base := by
    dsimp [AngularExteriorBounds.base, HarmonicSpatialMajorant.angularScale]
    positivity
  have he := envelope_nonnegative (a.1+1)
  have hcoef := coefBound_nonneg b B hb hB a
  have hApos := RiccatiSeriesCoefficients.amplitude_pos (a.1+1) 0
  set A := RiccatiSeriesCoefficients.amplitude (a.1+1) 0 with hAdef
  set ψ := regular (a.1+1) ‖x‖ with hψ
  set ψD := regularD (a.1+1) ‖x‖ with hψD
  obtain ⟨hE, hH⟩ := BackgroundFluxMajorant.eh_decomp_state (a.1+1) (modeP a) (modeP_hom a)
    ((((a.1+1 : ℕ) : ℝ)+1)*envelope (a.1+1)) (envelope (a.1+1)) (2*envelope (a.1+1))
    (fun n => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => poloidal_bound (a.1+1) a.2 n i))
    (fun n => scalar_value_bound (a.1+1) a.2 n)
    (fun n => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => toroidal_bound (a.1+1) a.2 n i))
    1 (by simp) (ψ : ℂ) (ψD : ℂ) x hx0
  have e1 : (fun i => SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) =
      fun i => Eform (a.1+1) (modeP a) 1 (ψ : ℂ) (ψD : ℂ) x i :=
    funext fun i => solidE_eq_Eform _ _ (modeP_hom a) (modeP_harm a) x hx0 i
  have e2 : (fun i => SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) =
      fun i => Hform (a.1+1) (modeP a) (ψ : ℂ) x i :=
    funext fun i => solidH_eq_Hform _ _ x hx0 i
  rw [e1, e2]
  have hu : 0 ≤ ((a.1 : ℝ)+2) := by positivity
  have hrest : 0 ≤ m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * C := by positivity
  have hp8 : ((a.1 : ℝ)+2)^8 ≤ ((a.1 : ℝ)+2)^9 :=
    pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg a.1 : (0:ℝ) ≤ a.1)]) (by norm_num)
  have hp7 : ((a.1 : ℝ)+2)^7 ≤ ((a.1 : ℝ)+2)^9 :=
    pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg a.1 : (0:ℝ) ≤ a.1)]) (by norm_num)
  have hp81 : ((a.1 : ℝ)+1)*((a.1 : ℝ)+2)^8 ≤ ((a.1 : ℝ)+2)^9 := by
    have : ((a.1 : ℝ)+2)^9 = ((a.1 : ℝ)+2)*((a.1 : ℝ)+2)^8 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hhalf : 0 ≤ (1/2 : ℝ)^(a.1+1) := by positivity
  have hψ0 : 0 ≤ |ψ| := abs_nonneg _
  have hψD0 : 0 ≤ |ψD| := abs_nonneg _
  have hn1 : ‖((ψD : ℝ) : ℂ)‖ = |ψD| := by simp
  have hn2 : ‖((ψ : ℝ) : ℂ)‖ = |ψ| := by simp
  have hKΘ1 : A * (B*AngularExteriorBounds.base)^(a.1+1) * mu * |ψD| ≤
      C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1) :=
    le_trans (by
      have : 0 ≤ A * (B*AngularExteriorBounds.base)^(a.1+1) * mu := by positivity
      nlinarith) hΘ
  have hKΘ2 : A * (B*AngularExteriorBounds.base)^(a.1+1) * mu * |ψ| ≤
      C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1) :=
    le_trans (by
      have : 0 ≤ A * (B*AngularExteriorBounds.base)^(a.1+1) * mu := by positivity
      nlinarith) hΘ
  refine ⟨?_, ?_⟩
  · have h1 := decomp_smul c hE
    refine decomp_mono hx0 h1 ?_ ?_
    · rw [hn1]
      calc ‖c‖ * (|ψD| * ((((a.1+1 : ℕ) : ℝ)+1)*envelope (a.1+1)))
          ≤ (m * coefBound b B a * mu) * (|ψD| * ((((a.1+1 : ℕ) : ℝ)+1)*envelope (a.1+1))) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * ((a.1 : ℝ)+2)^7 *
            (A * (B*AngularExteriorBounds.base)^(a.1+1) * mu * |ψD|) := by
            unfold coefBound
            rw [envelope_eq]
            push_cast
            ring
        _ ≤ m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * ((a.1 : ℝ)+2)^7 *
            (C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1)) :=
            mul_le_mul_of_nonneg_left hKΘ1 (by positivity)
        _ = m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * C * ((a.1 : ℝ)+2)^8 *
            (1/2 : ℝ)^(a.1+1) := by ring
        _ ≤ regConst b m C a := by
            unfold regConst
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp8 hrest) hhalf
    · rw [hn2]
      calc ‖c‖ * ((((a.1+1 : ℕ) : ℝ)*((((a.1+1 : ℕ) : ℝ))+1))* |ψ| * envelope (a.1+1))
          ≤ (m * coefBound b B a * mu) *
            ((((a.1+1 : ℕ) : ℝ)*((((a.1+1 : ℕ) : ℝ))+1))* |ψ| * envelope (a.1+1)) :=
            mul_le_mul_of_nonneg_right hc (by positivity)
        _ = m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale *
            (((a.1 : ℝ)+1)*((a.1 : ℝ)+2)^7) *
            (A * (B*AngularExteriorBounds.base)^(a.1+1) * mu * |ψ|) := by
            unfold coefBound
            rw [envelope_eq]
            push_cast
            ring
        _ ≤ m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale *
            (((a.1 : ℝ)+1)*((a.1 : ℝ)+2)^7) * (C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1)) :=
            mul_le_mul_of_nonneg_left hKΘ2 (by positivity)
        _ = m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * C *
            (((a.1 : ℝ)+1)*((a.1 : ℝ)+2)^8) * (1/2 : ℝ)^(a.1+1) := by ring
        _ ≤ regConst b m C a := by
            unfold regConst
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp81 hrest) hhalf
  · have h1 := decomp_smul c hH
    refine decomp_mono hx0 h1 ?_ (by simp)
    rw [hn2]
    calc ‖c‖ * (|ψ| * (2*envelope (a.1+1)))
        ≤ (m * coefBound b B a * mu) * (|ψ| * (2*envelope (a.1+1))) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 2 * (m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * ((a.1 : ℝ)+2)^6 *
          (A * (B*AngularExteriorBounds.base)^(a.1+1) * mu * |ψ|)) := by
          unfold coefBound
          rw [envelope_eq]
          ring
      _ ≤ 2 * (m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * ((a.1 : ℝ)+2)^6 *
          (C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKΘ2 (by positivity)) (by norm_num)
      _ = 2 * (m * DebyeJetBounds.scale 0 b * AngularExteriorBounds.scale * C * ((a.1 : ℝ)+2)^7 *
          (1/2 : ℝ)^(a.1+1)) := by ring
      _ ≤ 2 * regConst b m C a := by
          unfold regConst
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp7 hrest) hhalf) (by norm_num)

theorem regular_pair_decomp (b B m C mu1 mu2 : ℝ) (hb : 0 ≤ b) (hB : 0 ≤ B) (hm : 0 ≤ m) (hC : 0 ≤ C)
    (hmu1 : 0 ≤ mu1) (hmu2 : 0 ≤ mu2) (a : PositiveIndex) (α β : ℂ)
    (hα : ‖α‖ ≤ m * coefBound b B a * mu1) (hβ : ‖β‖ ≤ m * coefBound b B a * mu2) (x : Space)
    (hx0 : x ≠ 0)
    (hΘ1 : RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) * mu1 *
        (|regular (a.1+1) ‖x‖| + |regularD (a.1+1) ‖x‖|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1))
    (hΘ2 : RiccatiSeriesCoefficients.amplitude (a.1+1) 0 * (B*AngularExteriorBounds.base)^(a.1+1) * mu2 *
        (|regular (a.1+1) ‖x‖| + |regularD (a.1+1) ‖x‖|) ≤ C * ((a.1 : ℝ)+2) * (1/2 : ℝ)^(a.1+1)) :
    Decomp (3 * regConst b m C a) (regConst b m C a)
      (fun i => α * SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i +
        β * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) x ∧
    Decomp (3 * regConst b m C a) (regConst b m C a)
      (fun i => α * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i -
        β * SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) x := by
  obtain ⟨p1, p2⟩ := regular_piece b B m C mu1 hb hB hm hC hmu1 a α hα x hx0 hΘ1
  obtain ⟨q1, q2⟩ := regular_piece b B m C mu2 hb hB hm hC hmu2 a β hβ x hx0 hΘ2
  obtain ⟨r1, r2⟩ := regular_piece b B m C mu2 hb hB hm hC hmu2 a (-β) (by simpa using hβ) x hx0 hΘ2
  constructor
  · have h := decomp_add p1 q2
    have e : (fun i => α * SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i +
        β * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) =
        (α • fun i => SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) +
        (β • fun i => SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) := by
      funext i
      simp
    rw [e]
    exact decomp_mono hx0 h (by linarith) (by linarith)
  · have h := decomp_add p2 r1
    have e : (fun i => α * SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i -
        β * SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) =
        (α • fun i => SolidMaxwellProfiles.magnetic (a.1+1) (modeP a) x i) +
        ((-β) • fun i => SolidMaxwellProfiles.electric (a.1+1) (modeP a) x i) := by
      funext i
      simp
      ring
    rw [e]
    exact decomp_mono hx0 h (by linarith) (by linarith)

end OQ14.CoreRegularModes

#print axioms OQ14.CoreRegularModes.poly_geom_summable
#print axioms OQ14.CoreRegularModes.testMaxwell_solid
#print axioms OQ14.CoreRegularModes.weak_solid_tm
#print axioms OQ14.CoreRegularModes.weak_solid_te
#print axioms OQ14.CoreRegularModes.weak_solid_pair
#print axioms OQ14.CoreRegularModes.regConst_nonneg
#print axioms OQ14.CoreRegularModes.regConst_summable
#print axioms OQ14.CoreRegularModes.envelope_eq
#print axioms OQ14.CoreRegularModes.regular_piece
#print axioms OQ14.CoreRegularModes.regular_pair_decomp
