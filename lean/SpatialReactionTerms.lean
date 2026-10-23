import SpatialReactionMajorant

/-! Genuine joint spatial derivatives of the normalized solid-wave reaction terms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.SpatialReactionTerms
open OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.HarmonicSpatialMajorant
  OQ14.SpatialReactionMajorant OQ14.RiccatiSeriesCoefficients

def lowerJetScale (q : ℂ) (N : ℕ) (b : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N+1),jetScale q j b

theorem lowerJetScale_nonnegative (q : ℂ) (N : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    0 ≤ lowerJetScale q N b := Finset.sum_nonneg (fun j _ => jetScale_nonnegative q j b hb)

theorem jetScale_le_lowerJetScale (q : ℂ) (N j : ℕ) (b : ℝ) (hb : 0 ≤ b) (hj : j ≤ N) :
    jetScale q j b ≤ lowerJetScale q N b :=
  Finset.single_le_sum (fun i _ => jetScale_nonnegative q i b hb) (Finset.mem_range.mpr (by omega))

theorem degreeScale_mono (N j : ℕ) (b : ℝ) (hj : j ≤ N) : degreeScale j b ≤ degreeScale N b := by
  have ha : 0 ≤ angularScale := by dsimp [angularScale]; positivity
  apply mul_le_mul_of_nonneg_left _ ha
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _))

theorem linear_precomp_jet_norm_le (f : Space → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : (Space × Space) →L[ℝ] Space) (hL : ‖L‖ ≤ 1) (j : ℕ) (p : Space × Space) :
    ‖iteratedFDeriv ℝ j (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ j f (L p)‖ := by
  rw [L.iteratedFDeriv_comp_right hf p (by exact_mod_cast le_top)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)

def basisProduct (a : SphereHarmonicHilbert.TotalIndex) (u v : ℂ) (p : Space × Space) : ℂ :=
  SolidScalarHelmholtz.wave a.1 u (representative a.1 a.2) p.1*
    SolidScalarHelmholtz.wave a.1 v (representative a.1 a.2) p.2

theorem basisProduct_smooth (a : SphereHarmonicHilbert.TotalIndex) (u v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (basisProduct a u v) :=
  ((SolidScalarHelmholtz.wave_contDiff a.1 u _).comp contDiff_fst).mul
    ((SolidScalarHelmholtz.wave_contDiff a.1 v _).comp contDiff_snd)

theorem basisProduct_jet_bound (a : SphereHarmonicHilbert.TotalIndex) (u v : ℂ)
    (N j : ℕ) (hj : j ≤ N) (b B : ℝ) (hb : 0 ≤ b) (hB : 1 ≤ B)
    (hbB : degreeScale N b ≤ B) (p : Space × Space) (hp : ‖p‖ ≤ b) :
    ‖iteratedFDeriv ℝ j (basisProduct a u v) p‖ ≤
      2^N*(lowerJetScale u N b*lowerJetScale v N b)*
        (amplitude a.1 0)^2*(a.1+1 : ℝ)^6*B^(2*a.1) := by
  have hB0 := zero_le_one.trans hB
  have hu := lowerJetScale_nonnegative u N b hb
  have hv := lowerJetScale_nonnegative v N b hb
  have hA := (amplitude_pos a.1 0).le
  have hnorm (q : ℂ) (i : ℕ) (hi : i ≤ N) (x : Space) (hx : ‖x‖ ≤ b) :
      ‖iteratedFDeriv ℝ i (SolidScalarHelmholtz.wave a.1 q (representative a.1 a.2)) x‖ ≤
        lowerJetScale q N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1 := by
    have ht := normalized_wave_enlarged_bound a.1 a.2 q i b B hb
      ((degreeScale_mono N i b hi).trans hbB) x hx
    apply ht.trans
    gcongr
    exact jetScale_le_lowerJetScale q N i b hb hi
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space × Space => SolidScalarHelmholtz.wave a.1 u (representative a.1 a.2) z.1) :=
    (SolidScalarHelmholtz.wave_contDiff a.1 u (representative a.1 a.2)).comp contDiff_fst
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : Space × Space => SolidScalarHelmholtz.wave a.1 v (representative a.1 a.2) z.2) :=
    (SolidScalarHelmholtz.wave_contDiff a.1 v (representative a.1 a.2)).comp contDiff_snd
  have hprod : ‖iteratedFDeriv ℝ j (basisProduct a u v) p‖ ≤
      2^N*(lowerJetScale u N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1)*
        (lowerJetScale v N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j+1),(j.choose i : ℝ)*
          ‖iteratedFDeriv ℝ i (fun z : Space × Space => SolidScalarHelmholtz.wave a.1 u (representative a.1 a.2) z.1) p‖*
          ‖iteratedFDeriv ℝ (j-i) (fun z : Space × Space => SolidScalarHelmholtz.wave a.1 v (representative a.1 a.2) z.2) p‖ :=
        norm_iteratedFDeriv_mul_le hf hg p (by exact_mod_cast le_top)
      _ ≤ ∑ i ∈ Finset.range (j+1),(j.choose i : ℝ)*
          (lowerJetScale u N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1)*
          (lowerJetScale v N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN : i ≤ N := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hj
        have hjN : j-i ≤ N := (Nat.sub_le _ _).trans hj
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact (linear_precomp_jet_norm_le _ (SolidScalarHelmholtz.wave_contDiff _ _ _)
            (ContinuousLinearMap.fst ℝ Space Space) (ContinuousLinearMap.norm_fst_le ..) i p).trans
            (hnorm u i hiN p.1 ((norm_fst_le p).trans hp))
        · exact (linear_precomp_jet_norm_le _ (SolidScalarHelmholtz.wave_contDiff _ _ _)
            (ContinuousLinearMap.snd ℝ Space Space) (ContinuousLinearMap.norm_snd_le ..) (j-i) p).trans
            (hnorm v (j-i) hjN p.2 ((norm_snd_le p).trans hp))
        · exact norm_nonneg _
        · positivity
      _ = 2^j*(lowerJetScale u N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1)*
          (lowerJetScale v N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1) := by
        rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
      _ ≤ _ := by gcongr; norm_num
  convert hprod using 1; ring


def term (a : SphereHarmonicHilbert.TotalIndex) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0 < R) (u v : ℂ) : Space × Space → ℂ :=
  RadialSource.gamma a.1 gs R X hR • basisProduct a u v

theorem term_smooth (a : SphereHarmonicHilbert.TotalIndex) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0 < R) (u v : ℂ) : ContDiff ℝ (⊤ : ℕ∞) (term a gs R X hR u v) :=
  by simpa only [term,Pi.smul_apply] using (basisProduct_smooth a u v).const_smul (RadialSource.gamma a.1 gs R X hR)

theorem actual_joint_jet_bound (a : SphereHarmonicHilbert.TotalIndex)
    {gs : List RadialStack.Layer} {R X : ℝ}
    (hc : RadialStack.Chain gs X R) (q M d B : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hB : 1 ≤ B) (ht : Real.exp 1*B ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (hqp : ∀ g ∈ gs, g.q ≤ q)
    (u v : ℂ) (N j : ℕ) (hj : j ≤ N) (b : ℝ) (hb : 0 ≤ b)
    (hbB : degreeScale N b ≤ B) (p : Space × Space) (hp0 : ‖p‖ ≤ b) :
    ‖iteratedFDeriv ℝ j (term a gs R X (by linarith) u v) p‖ ≤
      (2^N*(lowerJetScale u N b*lowerJetScale v N b))*
        RadialFullMajorant.majorant q M d B 6 a.1 := by
  rw [term,iteratedFDeriv_const_smul_apply (by
    exact (basisProduct_smooth a u v).contDiffAt.of_le (by exact_mod_cast le_top))]
  apply (ContinuousMultilinearMap.opNorm_smul_le _ _).trans
  have hγ := mul_le_mul_of_nonneg_left (basisProduct_jet_bound a u v N j hj b B hb hB hbB p hp0)
    (norm_nonneg (RadialSource.gamma a.1 gs R X (by linarith)))
  have hrad := RiccatiImaginaryBound.gamma_weighted_amplitude_bound a.1 6 hc q M d B hq hM hR hB ht hX hd hp hqp
  have hC : 0 ≤ 2^N*(lowerJetScale u N b*lowerJetScale v N b) :=
    mul_nonneg (by positivity) (mul_nonneg (lowerJetScale_nonnegative u N b hb) (lowerJetScale_nonnegative v N b hb))
  calc
    _ ≤ (2^N*(lowerJetScale u N b*lowerJetScale v N b))*
        ((a.1+1 : ℝ)^6*‖RadialSource.gamma a.1 gs R X (by linarith)‖*(amplitude a.1 0)^2*B^(2*a.1)) := by
      convert hγ using 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrad hC

end OQ14.SpatialReactionTerms

#print axioms OQ14.SpatialReactionTerms.lowerJetScale_nonnegative

#print axioms OQ14.SpatialReactionTerms.jetScale_le_lowerJetScale

#print axioms OQ14.SpatialReactionTerms.degreeScale_mono

#print axioms OQ14.SpatialReactionTerms.linear_precomp_jet_norm_le

#print axioms OQ14.SpatialReactionTerms.basisProduct_smooth

#print axioms OQ14.SpatialReactionTerms.basisProduct_jet_bound

#print axioms OQ14.SpatialReactionTerms.term_smooth

#print axioms OQ14.SpatialReactionTerms.actual_joint_jet_bound
