import OutgoingDyadBounds

/-! Actual signed outgoing dyads have a summable uniform exterior envelope. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.OutgoingGeometricTail
open OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.AngularExteriorBounds OQ14.OutgoingDyadBounds

def prefactor (b R : ℝ) : ℝ := 4*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*Real.exp R
def majorant (b R : ℝ) (a : PositiveIndex) : ℝ := prefactor b R*(a.1+2 : ℝ)^8*(1/2 : ℝ)^(a.1+1)

theorem prefactor_nonnegative (b R : ℝ) (hb : 0≤b) : 0≤prefactor b R := by
  have h := DebyeJetBounds.scale_nonnegative 0 b hb
  have h' : 0≤AngularExteriorBounds.scale := by dsimp [AngularExteriorBounds.scale,HarmonicSpatialMajorant.areaScale];positivity
  dsimp [prefactor]
  positivity

theorem actual_uniform_bound (a : PositiveIndex) (b B R r : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R) (hBR : 2*(B*base)≤R) (hr : R≤r)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    ‖tmWeighted a r n y i j+teWeighted a r n y i j‖≤majorant b R a := by
  have hbase : 0≤base := by dsimp [base,HarmonicSpatialMajorant.angularScale];positivity
  have hC := DebyeJetBounds.scale_nonnegative 0 b hb
  have hS : 0≤AngularExteriorBounds.scale := by dsimp [AngularExteriorBounds.scale,HarmonicSpatialMajorant.areaScale];positivity
  have hrad := HankelExteriorBounds.regular_outgoing_geometric (a.1+1) (B*base) R r
    (mul_nonneg hB hbase) (by linarith) hBR hr
  have ht := tm_radial_bound a b B r hb hB hscale (by linarith) n y hy i j
  have he := te_radial_bound a b B r hb hB hscale (by linarith) n y hy i j
  have ht' : ‖tmWeighted a r n y i j‖≤
      2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*(a.1+2 : ℝ)^8*Real.exp R*(1/2 : ℝ)^(a.1+1) := by
    apply ht.trans
    calc
      _ = (DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*(a.1+2 : ℝ)^8)*
          (RiccatiSeriesCoefficients.amplitude (a.1+1) 0*(B*base)^(a.1+1)*‖ModalAlgebra.xiD (a.1+1) r‖+
           RiccatiSeriesCoefficients.amplitude (a.1+1) 0*(B*base)^(a.1+1)*‖ModalAlgebra.xi (a.1+1) r‖) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (add_le_add hrad.2 hrad.1) (by positivity)).trans_eq (by ring)
  have he' : ‖teWeighted a r n y i j‖≤
      2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*(a.1+2 : ℝ)^8*Real.exp R*(1/2 : ℝ)^(a.1+1) := by
    apply he.trans
    apply le_trans (mul_le_mul_of_nonneg_left hrad.1 (by positivity))
    have hp : (a.1+2 : ℝ)^6≤(a.1+2 : ℝ)^8 := by
      apply pow_le_pow_right₀ (by have h := Nat.cast_nonneg (α := ℝ) a.1;linarith)
      norm_num
    calc
      _ = (2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*Real.exp R*(1/2 : ℝ)^(a.1+1))*
          (a.1+2 : ℝ)^6 := by ring
      _ ≤ (2*DebyeJetBounds.scale 0 b*AngularExteriorBounds.scale*Real.exp R*(1/2 : ℝ)^(a.1+1))*
          (a.1+2 : ℝ)^8 := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by ring
  exact (norm_add_le _ _).trans ((add_le_add ht' he').trans_eq (by dsimp [majorant,prefactor];ring))

theorem majorant_summable (b R : ℝ) (hb : 0≤b) : Summable (majorant b R) := by
  have hC := prefactor_nonnegative b R hb
  apply (summable_sigma_of_nonneg (fun _ => by dsimp [majorant];positivity)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable,?_⟩
  simp only [tsum_fintype]
  have hs : Summable (fun n : ℕ => prefactor b R*(n+2 : ℝ)^11*(1/2 : ℝ)^(n+1)) := by
    have h := (RadialHighOrderTail.polynomial_geometric_summable 11).comp_injective Nat.succ_injective
    simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_assoc,
      mul_assoc,show (1 : ℝ)+1=2 by norm_num] using h.mul_left (prefactor b R)
  apply Summable.of_nonneg_of_le (fun _ => Finset.sum_nonneg (fun _ _ => by dsimp [majorant];positivity)) _ hs
  intro n
  have hcard : (Fintype.card (Index (n+1)) : ℝ)≤(n+2 : ℝ)^3 := by
    simpa only [Index,Fintype.card_fin,Nat.cast_pow,Nat.cast_add,Nat.cast_one,add_assoc,
      show (1 : ℝ)+1=2 by norm_num] using
      (Nat.cast_le (α := ℝ)).mpr (SphereHarmonicDimension.harmonicSpace_finrank_le (n+1))
  simp only [majorant,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  exact (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq (by ring)

theorem actual_summable (b B R r : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R) (hBR : 2*(B*base)≤R) (hr : R≤r)
    (n : Sphere) (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    Summable (fun a : PositiveIndex => tmWeighted a r n y i j+teWeighted a r n y i j) :=
  Summable.of_norm_bounded (majorant b R) (majorant_summable b R hb)
    (fun a => actual_uniform_bound a b B R r hb hB hscale hR hBR hr n y hy i j)

theorem uniform_series (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R) (hBR : 2*(B*base)≤R) (i j : Fin 3) :
    TendstoUniformlyOn
      (fun s : Finset PositiveIndex => fun p : ℝ × Sphere × Space =>
        ∑ a∈s,(tmWeighted a p.1 p.2.1 p.2.2 i j+teWeighted a p.1 p.2.1 p.2.2 i j))
      (fun p : ℝ × Sphere × Space => ∑' a : PositiveIndex,
        (tmWeighted a p.1 p.2.1 p.2.2 i j+teWeighted a p.1 p.2.1 p.2.2 i j))
      Filter.atTop {p : ℝ × Sphere × Space | R≤p.1 ∧ ‖p.2.2‖≤b} :=
  tendstoUniformlyOn_tsum (majorant_summable b R hb) (fun a (p : ℝ × Sphere × Space) hp =>
    actual_uniform_bound a b B R p.1 hb hB hscale hR hBR hp.1 p.2.1 p.2.2 hp.2 i j)

end OQ14.OutgoingGeometricTail

#print axioms OQ14.OutgoingGeometricTail.prefactor_nonnegative
#print axioms OQ14.OutgoingGeometricTail.actual_uniform_bound
#print axioms OQ14.OutgoingGeometricTail.majorant_summable
#print axioms OQ14.OutgoingGeometricTail.actual_summable
#print axioms OQ14.OutgoingGeometricTail.uniform_series
