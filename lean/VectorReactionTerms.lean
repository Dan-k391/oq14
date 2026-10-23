import DebyeJetBounds
import PhysicalReactionSeries

/-! Actual normalized regular vector dyads and compact joint derivative majorants. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.VectorReactionTerms
open Complex OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.SphereHarmonicHilbert
  OQ14.SpatialReactionTerms OQ14.HarmonicSpatialMajorant OQ14.RiccatiSeriesCoefficients

def component (tm : Bool) (a : TotalIndex) (i : Fin 3) : Space → ℂ :=
  if tm then fun x => DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave a.1 1 (representative a.1 a.2)) x i
  else fun x => DebyeCalculus.toroidal (SolidScalarHelmholtz.wave a.1 1 (representative a.1 a.2)) x i

theorem component_smooth (tm : Bool) (a : TotalIndex) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (component tm a i) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have ht := DebyeCalculus.toroidal_smooth _ x
    (SolidScalarHelmholtz.wave_contDiff a.1 1 (representative a.1 a.2)).contDiffAt
  cases tm
  · exact ht i
  · exact ExteriorClassical.curl_smooth _ ht i

theorem component_jet_bound (tm : Bool) (a : TotalIndex) (i : Fin 3)
    (N j : ℕ) (hj : j≤N) (b B : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hbB : degreeScale (N+2) b≤B) (x : Space) (hx : ‖x‖≤b) :
    ‖iteratedFDeriv ℝ j (component tm a i) x‖≤
      DebyeJetBounds.scale N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1 := by
  have h := DebyeJetBounds.normalized_vector_jet_bound a.1 a.2 N j hj b B hb hB hbB x hx i
  cases tm
  · exact h.1
  · exact h.2

def product (tm : Bool) (a : TotalIndex) (i j : Fin 3) (p : Space × Space) : ℂ :=
  component tm a i p.1*component tm a j p.2

theorem product_smooth (tm : Bool) (a : TotalIndex) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (product tm a i j) :=
  ((component_smooth tm a i).comp contDiff_fst).mul ((component_smooth tm a j).comp contDiff_snd)

theorem product_jet_bound (tm : Bool) (a : TotalIndex) (i j : Fin 3)
    (N m : ℕ) (hm : m≤N) (b B : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hbB : degreeScale (N+2) b≤B) (p : Space × Space) (hp : ‖p‖≤b) :
    ‖iteratedFDeriv ℝ m (product tm a i j) p‖≤
      (2^N*(DebyeJetBounds.scale N b)^2)*(amplitude a.1 0)^2*(a.1+1 : ℝ)^6*B^(2*a.1) := by
  let C := DebyeJetBounds.scale N b*amplitude a.1 0*(a.1+1 : ℝ)^3*B^a.1
  have hC : 0≤C := by
    have h := DebyeJetBounds.scale_nonnegative N b hb
    have h' := (amplitude_pos a.1 0).le
    dsimp [C]
    positivity
  have hf := (component_smooth tm a i).comp (contDiff_fst : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space × Space => p.1))
  have hg := (component_smooth tm a j).comp (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞) (fun p : Space × Space => p.2))
  have hleft (t : ℕ) (ht : t≤N) :
      ‖iteratedFDeriv ℝ t (fun z : Space × Space => component tm a i z.1) p‖≤C :=
    (linear_precomp_jet_norm_le _ (component_smooth tm a i)
      (ContinuousLinearMap.fst ℝ Space Space) (ContinuousLinearMap.norm_fst_le ..) t p).trans
        (component_jet_bound tm a i N t ht b B hb hB hbB p.1 ((norm_fst_le p).trans hp))
  have hright (t : ℕ) (ht : t≤N) :
      ‖iteratedFDeriv ℝ t (fun z : Space × Space => component tm a j z.2) p‖≤C :=
    (linear_precomp_jet_norm_le _ (component_smooth tm a j)
      (ContinuousLinearMap.snd ℝ Space Space) (ContinuousLinearMap.norm_snd_le ..) t p).trans
        (component_jet_bound tm a j N t ht b B hb hB hbB p.2 ((norm_snd_le p).trans hp))
  calc
    _ ≤ ∑ t ∈ Finset.range (m+1),(m.choose t : ℝ)*
        ‖iteratedFDeriv ℝ t (fun z : Space × Space => component tm a i z.1) p‖*
        ‖iteratedFDeriv ℝ (m-t) (fun z : Space × Space => component tm a j z.2) p‖ :=
      norm_iteratedFDeriv_mul_le hf hg p (by exact_mod_cast le_top)
    _ ≤ ∑ t ∈ Finset.range (m+1),(m.choose t : ℝ)*C*C := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (hleft t ((Nat.lt_succ_iff.mp (Finset.mem_range.mp ht)).trans hm)) (by positivity))
        (hright (m-t) ((Nat.sub_le _ _).trans hm)) (norm_nonneg _) (mul_nonneg (by positivity) hC)
    _ = 2^m*C*C := by
      rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ 2^N*C*C := by gcongr; norm_num
    _ = _ := by dsimp [C]; ring

def angularWeight (l : ℕ) : ℝ := ((l : ℝ)*(l+1))⁻¹

theorem angularWeight_bounds (l : ℕ) : 0≤angularWeight l ∧ angularWeight l≤1 := by
  have h0 : 0≤(l : ℝ)*(l+1) := by positivity
  refine ⟨inv_nonneg.mpr h0,?_⟩
  cases l with
  | zero => norm_num [angularWeight]
  | succ l =>
    apply inv_le_one_of_one_le₀
    have hl : 0≤(l : ℝ) := Nat.cast_nonneg l
    push_cast
    nlinarith

def term (tm : Bool) (a : TotalIndex) (i j : Fin 3) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0<R) : Space × Space → ℂ :=
  ((-(RadialSource.gamma a.1 gs R X hR+I))*(angularWeight a.1 : ℂ)) • product tm a i j

theorem term_smooth (tm : Bool) (a : TotalIndex) (i j : Fin 3) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0<R) : ContDiff ℝ (⊤ : ℕ∞) (term tm a i j gs R X hR) := by
  simpa only [term,Pi.smul_apply] using (product_smooth tm a i j).const_smul
    ((-(RadialSource.gamma a.1 gs R X hR+I))*(angularWeight a.1 : ℂ))

theorem actual_joint_jet_bound (tm : Bool) (a : TotalIndex) (i j : Fin 3)
    {gs : List RadialStack.Layer} {R X : ℝ} (hc : RadialStack.Chain gs X R)
    (q M d B : ℝ) (hq : 1≤q) (hM : 0≤M) (hR : 4≤R) (hB : 1≤B)
    (ht : Real.exp 1*B≤R) (hX : X≤2*R) (hd : X-R≤d)
    (hp : ∀ g∈gs,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M) (hqp : ∀ g∈gs,g.q≤q)
    (N m : ℕ) (hm : m≤N) (b : ℝ) (hb : 0≤b) (hbB : degreeScale (N+2) b≤B)
    (p : Space × Space) (hp0 : ‖p‖≤b) :
    ‖iteratedFDeriv ℝ m (term tm a i j gs R X (by linarith)) p‖≤
      (2^N*(DebyeJetBounds.scale N b)^2)*PhysicalReactionSeries.radialMajorant q M d B 6 a.1 := by
  have hw := angularWeight_bounds a.1
  have hnorm : ‖(-(RadialSource.gamma a.1 gs R X (by linarith)+I))*(angularWeight a.1 : ℂ)‖≤
      ‖-(RadialSource.gamma a.1 gs R X (by linarith)+I)‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hw.1]
    exact mul_le_of_le_one_right (norm_nonneg _) hw.2
  rw [term,iteratedFDeriv_const_smul_apply
    ((product_smooth tm a i j).contDiffAt.of_le (by exact_mod_cast le_top))]
  apply (ContinuousMultilinearMap.opNorm_smul_le _ _).trans
  have hprod := product_jet_bound tm a i j N m hm b B hb (zero_le_one.trans hB) hbB p hp0
  have hmul := mul_le_mul hnorm hprod (norm_nonneg _) (norm_nonneg _)
  have hrad := PhysicalReactionSeries.physical_amplitude_bound a.1 6 hc q M d B hq hM hR hB ht hX hd hp hqp
  calc
    _ ≤ (2^N*(DebyeJetBounds.scale N b)^2)*
        ((a.1+1 : ℝ)^6*‖-(RadialSource.gamma a.1 gs R X (by linarith)+I)‖*
          (amplitude a.1 0)^2*B^(2*a.1)) := by convert hmul using 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrad (by positivity)

end OQ14.VectorReactionTerms
#print axioms OQ14.VectorReactionTerms.component_smooth
#print axioms OQ14.VectorReactionTerms.component_jet_bound
#print axioms OQ14.VectorReactionTerms.product_smooth
#print axioms OQ14.VectorReactionTerms.product_jet_bound
#print axioms OQ14.VectorReactionTerms.angularWeight_bounds
#print axioms OQ14.VectorReactionTerms.term_smooth
#print axioms OQ14.VectorReactionTerms.actual_joint_jet_bound
