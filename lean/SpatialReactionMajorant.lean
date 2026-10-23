import HarmonicSpatialMajorant
import SphereHarmonicHilbert
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Actual mixed spatial jet products with a summable full-degree majorant. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.SpatialReactionMajorant
open OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.HarmonicSpatialMajorant
  OQ14.RiccatiSeriesCoefficients

def controlRadius (N P : ℕ) (b c : ℝ) : ℝ :=
  max 1 (max (degreeScale N b) (degreeScale P c))

theorem controlRadius_bounds (N P : ℕ) (b c : ℝ) :
    1 ≤ controlRadius N P b c ∧ degreeScale N b ≤ controlRadius N P b c ∧
      degreeScale P c ≤ controlRadius N P b c :=
  ⟨le_max_left _ _,(le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

theorem normalized_wave_enlarged_bound (l : ℕ) (i : Index l) (q : ℂ)
    (N : ℕ) (b B : ℝ) (hb : 0 ≤ b) (hB : degreeScale N b ≤ B)
    (x : Space) (hx : ‖x‖ ≤ b) :
    ‖iteratedFDeriv ℝ N (SolidScalarHelmholtz.wave l q (representative l i)) x‖ ≤
      jetScale q N b*amplitude l 0*(l+1 : ℝ)^3*B^l := by
  refine (normalized_wave_jet_bound l i q N b hb x hx).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (degreeScale_nonnegative N b) hB l)
    (mul_nonneg (mul_nonneg (jetScale_nonnegative q N b hb) (amplitude_pos l 0).le) (by positivity))

theorem actual_mixed_jet_bound (l : ℕ) (i : Index l) {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (u v : ℂ) (N P : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hc0 : 0 ≤ c)
    (hbB : degreeScale N b ≤ B) (hcB : degreeScale P c ≤ B)
    (x y : Space) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) :
    ‖RadialSource.gamma l gs R X (by linarith)‖*
      ‖iteratedFDeriv ℝ N (SolidScalarHelmholtz.wave l u (representative l i)) x‖*
      ‖iteratedFDeriv ℝ P (SolidScalarHelmholtz.wave l v (representative l i)) y‖ ≤
      (jetScale u N b*jetScale v P c)*RadialFullMajorant.majorant q M d B 6 l := by
  have hleft := normalized_wave_enlarged_bound l i u N b B hb hbB x hx
  have hright := normalized_wave_enlarged_bound l i v P c B hc0 hcB y hy
  have hL := jetScale_nonnegative u N b hb
  have hV := jetScale_nonnegative v P c hc0
  have hA := (amplitude_pos l 0).le
  have hB0 := zero_le_one.trans hB
  have hprod := mul_le_mul hleft hright (norm_nonneg _)
    (by positivity : 0 ≤ jetScale u N b*amplitude l 0*(l+1 : ℝ)^3*B^l)
  have hγ := mul_le_mul_of_nonneg_left hprod
    (norm_nonneg (RadialSource.gamma l gs R X (by linarith)))
  have hrad := RiccatiImaginaryBound.gamma_weighted_amplitude_bound l 6 hc q M d B hq hM
    hR hB ht hX hd hp hqp
  calc
    _ ≤ (jetScale u N b*jetScale v P c)*
        ((l+1 : ℝ)^6*‖RadialSource.gamma l gs R X (by linarith)‖*(amplitude l 0)^2*B^(2*l)) := by
      convert hγ using 1 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrad (mul_nonneg hL hV)


theorem majorant_weight_shift (q M d B : ℝ) (k n l : ℕ) :
    RadialFullMajorant.majorant q M d B (k+n) l=
      (l+1 : ℝ)^n*RadialFullMajorant.majorant q M d B k l := by
  simp only [RadialFullMajorant.majorant,RadialLowTail.majorant,RadialMiddleTail.majorant,pow_add]
  ring

theorem actual_degree_jet_bound (l : ℕ) {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (u v : ℂ) (N P : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hc0 : 0 ≤ c)
    (hbB : degreeScale N b ≤ B) (hcB : degreeScale P c ≤ B)
    (x y : Space) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) :
    (∑ i : Index l,‖RadialSource.gamma l gs R X (by linarith)‖*
      ‖iteratedFDeriv ℝ N (SolidScalarHelmholtz.wave l u (representative l i)) x‖*
      ‖iteratedFDeriv ℝ P (SolidScalarHelmholtz.wave l v (representative l i)) y‖) ≤
      (jetScale u N b*jetScale v P c)*RadialFullMajorant.majorant q M d B 9 l := by
  have hJ := mul_nonneg (jetScale_nonnegative u N b hb) (jetScale_nonnegative v P c hc0)
  have hcard : (Fintype.card (Index l) : ℝ) ≤ (l+1 : ℝ)^3 := by
    simpa only [Index,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one] using
      (Nat.cast_le (α := ℝ)).mpr (SphereHarmonicDimension.harmonicSpace_finrank_le l)
  calc
    _ ≤ ∑ _i : Index l,(jetScale u N b*jetScale v P c)*RadialFullMajorant.majorant q M d B 6 l := by
      apply Finset.sum_le_sum
      intro i _
      exact actual_mixed_jet_bound l i hc q M d B hq hM hR hB ht hX hd hp hqp
        u v N P b c hb hc0 hbB hcB x y hx hy
    _ = (Fintype.card (Index l) : ℝ)*((jetScale u N b*jetScale v P c)*
        RadialFullMajorant.majorant q M d B 6 l) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    _ ≤ (l+1 : ℝ)^3*((jetScale u N b*jetScale v P c)*RadialFullMajorant.majorant q M d B 6 l) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg hJ (RadialFullMajorant.majorant_nonnegative _ _ _ _ _ _))
    _ = _ := by rw [show (9 : ℕ)=6+3 by norm_num,majorant_weight_shift];ring

theorem actual_mixed_norm_summable {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (u v : ℂ) (N P : ℕ) (b c : ℝ) (hb : 0 ≤ b) (hc0 : 0 ≤ c)
    (hbB : degreeScale N b ≤ B) (hcB : degreeScale P c ≤ B)
    (x y : Space) (hx : ‖x‖ ≤ b) (hy : ‖y‖ ≤ c) :
    Summable (fun a : SphereHarmonicHilbert.TotalIndex =>
      ‖RadialSource.gamma a.1 gs R X (by linarith)‖*
      ‖iteratedFDeriv ℝ N (SolidScalarHelmholtz.wave a.1 u (representative a.1 a.2)) x‖*
      ‖iteratedFDeriv ℝ P (SolidScalarHelmholtz.wave a.1 v (representative a.1 a.2)) y‖) := by
  apply (summable_sigma_of_nonneg (fun _ => by positivity)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable,?_⟩
  simp only [tsum_fintype]
  apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => by positivity))
    (fun l => actual_degree_jet_bound l hc q M d B hq hM hR hB ht hX hd hp hqp
      u v N P b c hb hc0 hbB hcB x y hx hy)
  exact (RadialFullMajorant.majorant_summable q M d B 9 (zero_le_one.trans hB)).mul_left _

end OQ14.SpatialReactionMajorant

#print axioms OQ14.SpatialReactionMajorant.controlRadius_bounds

#print axioms OQ14.SpatialReactionMajorant.normalized_wave_enlarged_bound

#print axioms OQ14.SpatialReactionMajorant.actual_mixed_jet_bound

#print axioms OQ14.SpatialReactionMajorant.majorant_weight_shift

#print axioms OQ14.SpatialReactionMajorant.actual_degree_jet_bound

#print axioms OQ14.SpatialReactionMajorant.actual_mixed_norm_summable
