import VectorLimitJets

/-! Compact joint-jet convergence of the literal paired Maxwell mode series to the actual central kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PairedVectorKernelLimit
open Filter Set Metric Complex OQ14.Maxwell OQ14.SphereHarmonicHilbert
  OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit OQ14.HarmonicSpatialMajorant
  OQ14.VectorLimitIdentification
open PhysicalReactionLimit (Region Jet region_norm)
open scoped Topology

def actualJetMap (q : ℝ) (hq : 0<q) (n m : ℕ) (b : ℝ) (i j : Fin 3) (R : ℕ) : C(Region b,Jet m) :=
  (∑' a,VectorReactionLimit.actualMap true i j (RadialPairedFamily.tm q hq n) m b R a)+
    (∑' a,VectorReactionLimit.actualMap false i j (RadialPairedFamily.te q hq n) m b R a)

def kernelJetMap (q : ℝ) (hq : 0<q) (n m : ℕ) (b : ℝ) (i j : Fin 3) : C(Region b,Jet m) :=
  (∑' a,VectorReactionLimit.limitMap true i j (RadialPairedFamily.tm q hq n) m b a)+
    (∑' a,VectorReactionLimit.limitMap false i j (RadialPairedFamily.te q hq n) m b a)

theorem kernelJetMap_apply (q : ℝ) (hq : 1≤q) (n m : ℕ) (b : ℝ) (hb : 0≤b)
    (i j : Fin 3) (p : Region b) :
    kernelJetMap q (zero_lt_one.trans_le hq) n m b i j p=
      iteratedFDeriv ℝ m (kernel q n i j) p.val := by
  let te := RadialPairedFamily.te q (zero_lt_one.trans_le hq) n
  let tm := RadialPairedFamily.tm q (zero_lt_one.trans_le hq) n
  let B := max 1 (degreeScale (m+2) b)
  have hq2 : 1≤q^2 := by nlinarith
  have hte := RadialPairedFamily.pairs_parameters q 1 hq le_rfl hq2 n
  have htm := RadialPairedFamily.pairs_parameters q (q^2) hq hq2 le_rfl n
  have hst := VectorReactionLimit.limiting_summable true i j tm q (q^2) b B m hq
    (sq_nonneg q) hb (le_max_left _ _) (le_max_right _ _) htm
  have hse := VectorReactionLimit.limiting_summable false i j te q (q^2) b B m hq
    (sq_nonneg q) hb (le_max_left _ _) (le_max_right _ _) hte
  have het : (∑' a,VectorReactionLimit.limitMap true i j tm m b a) p=
      ∑' a,iteratedFDeriv ℝ m (limitTerm true i j tm a) p.val := by
    simpa only [ContinuousMap.evalCLM_apply,VectorLimitJets.limitMap_apply] using
      (ContinuousMap.evalCLM ℂ p).map_tsum hst
  have hee : (∑' a,VectorReactionLimit.limitMap false i j te m b a) p=
      ∑' a,iteratedFDeriv ℝ m (limitTerm false i j te a) p.val := by
    simpa only [ContinuousMap.evalCLM_apply,VectorLimitJets.limitMap_apply] using
      (ContinuousMap.evalCLM ℂ p).map_tsum hse
  have hdt := VectorLimitJets.derivative_summable true i j tm q (q^2) b m hq (sq_nonneg q) hb htm p.val (region_norm b p)
  have hde := VectorLimitJets.derivative_summable false i j te q (q^2) b m hq (sq_nonneg q) hb hte p.val (region_norm b p)
  calc
    _ = (∑' a,iteratedFDeriv ℝ m (limitTerm true i j tm a) p.val)+
        (∑' a,iteratedFDeriv ℝ m (limitTerm false i j te a) p.val) := by
      change ((∑' a,VectorReactionLimit.limitMap true i j tm m b a) p)+
        ((∑' a,VectorReactionLimit.limitMap false i j te m b a) p)=_
      rw [het,hee]
    _ = ∑' a,iteratedFDeriv ℝ m (fun z => combinedTerm q (zero_lt_one.trans_le hq) n i j z a) p.val := by
      rw [← hdt.tsum_add hde]
      apply tsum_congr
      intro a
      change _=iteratedFDeriv ℝ m (limitTerm true i j tm a+limitTerm false i j te a) p.val
      exact (iteratedFDeriv_add_apply
        ((VectorLimitJets.limitTerm_smooth true i j tm a).contDiffAt.of_le (by exact_mod_cast le_top))
        ((VectorLimitJets.limitTerm_smooth false i j te a).contDiffAt.of_le (by exact_mod_cast le_top))).symm
    _ = _ := (VectorLimitJets.paired_derivative_series q hq n m i j (b+1) (by linarith)
      p.val (by have h := region_norm b p;linarith)).symm

theorem uniform_kernel_jet_limit (q : ℝ) (hq : 1≤q) (n m : ℕ) (b : ℝ) (hb : 0≤b) (i j : Fin 3) :
    Tendsto (actualJetMap q (zero_lt_one.trans_le hq) n m b i j) atTop
      (𝓝 (kernelJetMap q (zero_lt_one.trans_le hq) n m b i j)) := by
  let B := max 1 (degreeScale (m+2) b)
  have hq2 : 1≤q^2 := by nlinarith
  exact (VectorReactionLimit.uniform_physical_jet_limit true i j
    (RadialPairedFamily.tm q (zero_lt_one.trans_le hq) n) q (q^2) b B m hq (sq_nonneg q) hb
    (le_max_left _ _) (le_max_right _ _)
    (RadialPairedFamily.pairs_parameters q (q^2) hq hq2 le_rfl n)).add
      (VectorReactionLimit.uniform_physical_jet_limit false i j
        (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n) q (q^2) b B m hq (sq_nonneg q) hb
        (le_max_left _ _) (le_max_right _ _)
        (RadialPairedFamily.pairs_parameters q 1 hq le_rfl hq2 n))

theorem eventually_actual_apply (q : ℝ) (hq : 1≤q) (n m : ℕ) (b : ℝ) (hb : 0≤b) (i j : Fin 3) :
    ∀ᶠ R : ℕ in atTop,∀ p : Region b,
      actualJetMap q (zero_lt_one.trans_le hq) n m b i j R p=
        iteratedFDeriv ℝ m (VectorReactionSeries.series true i j
          (layers (RadialPairedFamily.tm q (zero_lt_one.trans_le hq) n) (radius R) (radius_pos R))
          (radius R) (radius R+width (RadialPairedFamily.tm q (zero_lt_one.trans_le hq) n)) (radius_pos R)) p.val+
        iteratedFDeriv ℝ m (VectorReactionSeries.series false i j
          (layers (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n) (radius R) (radius_pos R))
          (radius R) (radius R+width (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n)) (radius_pos R)) p.val := by
  let B := max 1 (max (degreeScale (m+2) b) (degreeScale (m+2) (b+1)))
  have hB : 1≤B := le_max_left _ _
  have hbB : degreeScale (m+2) b≤B := (le_max_left _ _).trans (le_max_right _ _)
  have hpB : degreeScale (m+2) (b+1)≤B := (le_max_right _ _).trans (le_max_right _ _)
  have hq2 : 1≤q^2 := by nlinarith
  filter_upwards [VectorReactionLimit.eventually_sum_eq_actual_derivative true i j
    (RadialPairedFamily.tm q (zero_lt_one.trans_le hq) n) q (q^2) b B m hq (sq_nonneg q) hb hB hbB hpB
    (RadialPairedFamily.pairs_parameters q (q^2) hq hq2 le_rfl n),
    VectorReactionLimit.eventually_sum_eq_actual_derivative false i j
      (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n) q (q^2) b B m hq (sq_nonneg q) hb hB hbB hpB
      (RadialPairedFamily.pairs_parameters q 1 hq le_rfl hq2 n)] with R ht he
  intro p
  simp only [actualJetMap,ContinuousMap.add_apply,ht p,he p]

end OQ14.PairedVectorKernelLimit

#print axioms OQ14.PairedVectorKernelLimit.kernelJetMap_apply
#print axioms OQ14.PairedVectorKernelLimit.uniform_kernel_jet_limit
#print axioms OQ14.PairedVectorKernelLimit.eventually_actual_apply
