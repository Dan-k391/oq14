import Packet05DifferenceConverse
import RegionalMaxwellHelmholtz
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Packet05FlatWeight
import Packet05DivergenceUpgrade

/-! Weak derivatives preserve a constant relation on open material phases. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05LocalDerivative
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact
open scoped Topology

theorem weak_partial_local_constant_relation (U : Set Space) (hU : IsOpen U)
    (f g Df Dg : L2Scalar) (a : ℂ) (i : Fin 3)
    (hf : HasWeakPartial f Df i) (hg : HasWeakPartial g Dg i)
    (hfg : ∀ᵐ x ∂volume, x ∈ U → g x = a * f x) :
    ∀ᵐ x ∂volume, x ∈ U → Dg x = a * Df x := by
  let Z : L2Scalar := Dg - a • Df
  have hz : ∀ᵐ x ∂volume, x ∈ U → Z x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((Lp.memLp Z).locallyIntegrable (by norm_num)).locallyIntegrableOn U)
    intro v hv hvc hvs
    let φ : Test := ⟨fun x => (v x : ℂ),
      (Complex.ofRealCLM.contDiff.comp hv).of_le (by simp),
      hvc.comp_left Complex.ofRealCLM.map_zero⟩
    have hφU : tsupport φ.function ⊆ U := by
      apply (closure_mono ?_).trans hvs
      intro x hx
      change (v x : ℂ) ≠ 0 at hx
      change v x ≠ 0
      exact fun hvx => hx (by simp [hvx])
    have he : derivativePair φ i g = a * derivativePair φ i f := by
      simp only [derivativePair, testPair_integral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hfg] with x hx
      by_cases hxu : x ∈ U
      · rw [hx hxu]
        ring
      · have hz : dcoord φ.function x i = 0 := by
          have hnot : x ∉ tsupport φ.function := fun hx => hxu (hφU hx)
          simp [dcoord, fderiv_of_not_mem_tsupport ℝ hnot]
        simp [hz]
    have hhf := hf φ
    have hhg := hg φ
    have hvpair : valuePair φ Dg - a * valuePair φ Df = 0 := by
      rw [he] at hhg
      linear_combination hhg - a * hhf
    have hZ : valuePair φ Z = 0 := by
      simp only [Z, map_sub, map_smul, smul_eq_mul]
      exact hvpair
    rw [valuePair, testPair_integral] at hZ
    convert hZ using 1
    apply integral_congr_ae
    filter_upwards with x
    simp [φ, smul_eq_mul, mul_comm]
  filter_upwards [hz, Lp.coeFn_sub Dg (a • Df), Lp.coeFn_smul a Df] with x hx hs hm hxu
  have hzero := hx hxu
  change (Dg - a • Df : L2Scalar) x = 0 at hzero
  rw [hs] at hzero
  simp only [Pi.sub_apply] at hzero
  rw [hm] at hzero
  simp only [Pi.smul_apply, smul_eq_mul] at hzero
  exact sub_eq_zero.mp hzero

theorem weak_partial_unique (u D1 D2 : L2Scalar) (i : Fin 3)
    (h1 : HasWeakPartial u D1 i) (h2 : HasWeakPartial u D2 i) : D1 = D2 := by
  have he := weak_partial_local_constant_relation Set.univ isOpen_univ u u D1 D2 1 i h1 h2
    (by filter_upwards with x hx; simp)
  apply Lp.ext
  filter_upwards [he] with x hx
  simpa using (hx (Set.mem_univ x)).symm

/-- On either open flat phase the differentiated electric displacement is
the same constant dielectric times the differentiated electric field. -/
theorem weighted_partial_on_constant_phase (U : Set Space) (hU : IsOpen U)
    (d : ℝ) (hd : 0 ≤ d) (ε₀ : ℝ) (hε : ∀ x ∈ U,
      FlatDifferenceCoercivity.dielectric d x = ε₀)
    (u Du Dwu : L2Scalar) (i : Fin 3)
    (hu : HasWeakPartial u Du i)
    (hwu : HasWeakPartial (Packet05FlatWeight.mulWeight d hd u) Dwu i) :
    ∀ᵐ x ∂volume, x ∈ U → Dwu x = (ε₀ : ℂ) * Du x := by
  apply weak_partial_local_constant_relation U hU u (Packet05FlatWeight.mulWeight d hd u)
    Du Dwu (ε₀ : ℂ) i hu hwu
  filter_upwards [Packet05FlatWeight.mulWeight_ae d hd u] with x hx hxu
  rw [hx]
  simp [Packet05FlatWeight.weight, hε x hxu]

theorem interface_plane_null : volume {x : Space | x 2 = 0} = 0 := by
  let p : Space →ₗ[ℝ] ℝ := (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).toLinearMap
  have hp : LinearMap.ker p ≠ ⊤ := by
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    have he := congrArg (fun f : Space →ₗ[ℝ] ℝ => f (basis 2)) h
    simp [p, basis, EuclideanSpace.single_apply] at he
  have hn := Measure.addHaar_submodule volume (LinearMap.ker p) hp
  convert hn using 1

/-- Once both weak partials exist, the tangentially invariant flat jump
commutes with them globally, including across the null interface. -/
theorem weighted_partial_eq (d : ℝ) (hd : 0 ≤ d) (u Du Dwu : L2Scalar)
    (i : Fin 3) (hu : HasWeakPartial u Du i)
    (hwu : HasWeakPartial (Packet05FlatWeight.mulWeight d hd u) Dwu i) :
    Dwu = Packet05FlatWeight.mulWeight d hd Du := by
  have hm : IsOpen {x : Space | x 2 < 0} :=
    isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const
  have hp : IsOpen {x : Space | 0 < x 2} :=
    isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous
  have hminus := weighted_partial_on_constant_phase _ hm d hd 1
    (fun x hx => by change x 2 < 0 at hx; simp [FlatDifferenceCoercivity.dielectric, hx]) u Du Dwu i hu hwu
  have hplus := weighted_partial_on_constant_phase _ hp d hd (1+d)
    (fun x hx => by change 0 < x 2 at hx; simp [FlatDifferenceCoercivity.dielectric, not_lt.mpr hx.le]) u Du Dwu i hu hwu
  have hplane : ∀ᵐ x : Space ∂volume, x 2 ≠ 0 := by
    rw [ae_iff]
    simpa using interface_plane_null
  apply Lp.ext
  filter_upwards [hminus, hplus, hplane, Packet05FlatWeight.mulWeight_ae d hd Du] with x hm hp hn hw
  rw [hw]
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have he := hm hlt
    simp [Packet05FlatWeight.weight, FlatDifferenceCoercivity.dielectric, hlt, he]
  · have he := hp hgt
    simp [Packet05FlatWeight.weight, FlatDifferenceCoercivity.dielectric, not_lt.mpr hgt.le, he]

/-- A weak derivative of the displacement gives the corresponding derivative
of E on each nonzero constant material phase, with an L² representative. -/
theorem weighted_partial_gives_phase_partial (U : Set Space) (d : ℝ) (hd : 0 ≤ d)
    (ε₀ : ℝ) (hε₀ : ε₀ ≠ 0)
    (hε : ∀ x ∈ U, FlatDifferenceCoercivity.dielectric d x = ε₀)
    (u Dwu : L2Scalar) (i : Fin 3)
    (hwu : HasWeakPartial (Packet05FlatWeight.mulWeight d hd u) Dwu i) :
    ∀ (φ : Test), tsupport φ.function ⊆ U →
      valuePair φ (((ε₀ : ℂ)⁻¹) • Dwu) + derivativePair φ i u = 0 := by
  intro φ hφU
  have he : derivativePair φ i (Packet05FlatWeight.mulWeight d hd u) =
      (ε₀ : ℂ) * derivativePair φ i u := by
    simp only [derivativePair, testPair_integral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Packet05FlatWeight.mulWeight_ae d hd u] with x hx
    by_cases hxu : x ∈ U
    · rw [hx]
      simp only [Packet05FlatWeight.weight, hε x hxu]
      ring
    · have hnot : x ∉ tsupport φ.function := fun hx => hxu (hφU hx)
      have hz : dcoord φ.function x i = 0 := by simp [dcoord, fderiv_of_not_mem_tsupport ℝ hnot]
      simp [hz]
  have hh := hwu φ
  rw [he] at hh
  simp only [map_smul, smul_eq_mul]
  have hn : (ε₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε₀
  have hh' := congrArg (fun z : ℂ => (ε₀ : ℂ)⁻¹ * z) hh
  simp only [mul_add, ← mul_assoc, inv_mul_cancel₀ hn, one_mul, mul_zero] at hh'
  exact hh'

/-- An L² weak divergence equals the sum of already existing L² partials. -/
theorem divergence_eq_sum_partials (W : L2Vector) (D G0 G1 G2 : L2Scalar)
    (hdiv : HasWeakDivergence W D)
    (h0 : HasWeakPartial (W 0) G0 0) (h1 : HasWeakPartial (W 1) G1 1)
    (h2 : HasWeakPartial (W 2) G2 2) : D = G0 + G1 + G2 := by
  have hn := Packet05DivergenceUpgrade.normal_from_divergence W D G0 G1 hdiv h0 h1
  have he := weak_partial_local_constant_relation Set.univ isOpen_univ (W 2) (W 2)
    G2 (D-G0-G1) 1 2 h2 hn (by filter_upwards with x hx; simp)
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_sub (D-G0) G1, Lp.coeFn_sub D G0,
    Lp.coeFn_add (G0+G1) G2, Lp.coeFn_add G0 G1] with x he hsub1 hsub0 hadd1 hadd0
  have hx := he (Set.mem_univ x)
  change (D-G0-G1 : L2Scalar) x = _ at hx
  rw [hsub1] at hx
  simp only [Pi.sub_apply, one_mul] at hx
  rw [hsub0] at hx
  simp only [Pi.sub_apply] at hx
  rw [hadd1]
  simp only [Pi.add_apply]
  rw [hadd0]
  simp only [Pi.add_apply]
  linear_combination hx

/-- A global weak derivative transfers to any field agreeing almost
everywhere on the test region. -/
theorem local_partial_of_ae_eq (U : Set Space) (f g Dg : L2Scalar) (i : Fin 3)
    (hg : HasWeakPartial g Dg i) (hfg : ∀ᵐ x ∂volume, x ∈ U → f x = g x) :
    ∀ (φ : Test), tsupport φ.function ⊆ U →
      valuePair φ Dg + derivativePair φ i f = 0 := by
  intro φ hφU
  have he : derivativePair φ i f = derivativePair φ i g := by
    simp only [derivativePair, testPair_integral]
    apply integral_congr_ae
    filter_upwards [hfg] with x hx
    by_cases hxu : x ∈ U
    · rw [hx hxu]
    · have hnot : x ∉ tsupport φ.function := fun hx => hxu (hφU hx)
      have hz : dcoord φ.function x i = 0 := by simp [dcoord, fderiv_of_not_mem_tsupport ℝ hnot]
      simp [hz]
  rw [he]
  exact hg φ

/-- The normal displacement derivative is minus the dielectric times the
tangential divergence wherever the actual weighted divergence vanishes. -/
theorem normal_displacement_from_divergence (U : Set Space) (d : ℝ) (hd : 0 ≤ d)
    (F : L2Vector) (D A0 A1 B0 B1 N : L2Scalar)
    (hdiv : HasWeakDivergence (fun j => Packet05FlatWeight.mulWeight d hd (F j)) D)
    (hzero : ∀ᵐ x ∂volume, x ∈ U → D x = 0)
    (ha0 : HasWeakPartial (F 0) A0 0) (ha1 : HasWeakPartial (F 1) A1 1)
    (hb0 : HasWeakPartial (Packet05FlatWeight.mulWeight d hd (F 0)) B0 0)
    (hb1 : HasWeakPartial (Packet05FlatWeight.mulWeight d hd (F 1)) B1 1)
    (hn : HasWeakPartial (Packet05FlatWeight.mulWeight d hd (F 2)) N 2) :
    ∀ᵐ x ∂volume, x ∈ U →
      N x = -(Packet05FlatWeight.weight d x) * (A0 x + A1 x) := by
  have hb0' := weighted_partial_eq d hd (F 0) A0 B0 0 ha0 hb0
  have hb1' := weighted_partial_eq d hd (F 1) A1 B1 1 ha1 hb1
  have heq := divergence_eq_sum_partials _ D B0 B1 N hdiv hb0 hb1 hn
  have hae := (Lp.coeFn_add (B0+B1) N)
  have hbe := (Lp.coeFn_add B0 B1)
  filter_upwards [hzero, hae, hbe, Packet05FlatWeight.mulWeight_ae d hd A0,
    Packet05FlatWeight.mulWeight_ae d hd A1] with x hz ha hb hw0 hw1 hx
  have hDx : D x = (B0+B1+N : L2Scalar) x := congrArg (fun v : L2Scalar => v x) heq
  rw [ha] at hDx
  simp only [Pi.add_apply] at hDx
  rw [hb] at hDx
  simp only [Pi.add_apply] at hDx
  rw [hb0', hb1', hw0, hw1, hz hx] at hDx
  linear_combination -hDx

end OQ14.Packet05LocalDerivative
#print axioms OQ14.Packet05LocalDerivative.weak_partial_local_constant_relation
#print axioms OQ14.Packet05LocalDerivative.weak_partial_unique
#print axioms OQ14.Packet05LocalDerivative.weighted_partial_on_constant_phase
#print axioms OQ14.Packet05LocalDerivative.interface_plane_null
#print axioms OQ14.Packet05LocalDerivative.weighted_partial_eq
#print axioms OQ14.Packet05LocalDerivative.weighted_partial_gives_phase_partial
#print axioms OQ14.Packet05LocalDerivative.divergence_eq_sum_partials
#print axioms OQ14.Packet05LocalDerivative.local_partial_of_ae_eq
#print axioms OQ14.Packet05LocalDerivative.normal_displacement_from_divergence
