import SourceTensorSeries

/-! Every joint spatial derivative of the actual core tensor is the physical vector-mode derivative sum. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.SourceTensorJets
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceDielectricModes
open OQ14.SourceModeDatum OQ14.SphereHarmonicHilbert OQ14.HarmonicSpatialMajorant OQ14.SourceTensorSeries

theorem jet_eq_of_eventuallyEq (f g : Space × Space → ℂ) (p : Space × Space)
    (h : f=ᶠ[nhds p] g) (m : ℕ) : iteratedFDeriv ℝ m f p=iteratedFDeriv ℝ m g p := by
  have hw : f=ᶠ[nhdsWithin p univ] g := by simpa only [nhdsWithin_univ] using h
  simpa only [iteratedFDerivWithin_univ] using hw.iteratedFDerivWithin_eq h.self_of_nhds m

theorem term_smooth (d : Data) (a : TotalIndex) (i j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (term d a i j) :=
  (VectorReactionTerms.term_smooth true a i j d.gs d.R d.X d.hR).add
    (VectorReactionTerms.term_smooth false a i j (d.gs.map teLayer) d.R d.X d.hR)

theorem te_bounds (d : Data) (q M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M) (hdisp : ∀ g∈d.gs,g.q^2=g.σ)
    (hqp : ∀ g∈d.gs,g.q≤q) :
    (∀ g∈d.gs.map teLayer,1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M) ∧ (∀ g∈d.gs.map teLayer,g.q≤q) := by
  constructor
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact ⟨le_rfl,hM,by change a.q^2≤M; rw [hdisp a ha]; exact (hs a ha).2⟩
  · intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    exact hqp a ha

theorem series_derivative (d : Data) (q M B : ℝ) (hq : 1≤q) (hM : 1≤M)
    (hR : 4≤d.R) (hB : 1≤B) (ht : Real.exp 1*B≤d.R) (hX : d.X≤2*d.R)
    (hs : ∀ g∈d.gs,1≤g.σ ∧ g.σ≤M) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hqp : ∀ g∈d.gs,g.q≤q)
    (N m : ℕ) (hm : m≤N) (b : ℝ) (hb : 0<b) (hbB : degreeScale (N+2) b≤B)
    (p : Space × Space) (hp : ‖p‖<b) (i j : Fin 3) :
    iteratedFDeriv ℝ m (series d i j) p=
      iteratedFDeriv ℝ m (VectorReactionSeries.series true i j d.gs d.R d.X d.hR) p+
        iteratedFDeriv ℝ m (VectorReactionSeries.series false i j (d.gs.map teLayer) d.R d.X d.hR) p := by
  have hM0 : 0≤M := zero_le_one.trans hM
  have htm (g : RadialStack.Layer) (hg : g∈d.gs) : 1≤g.σ ∧ g.σ≤M ∧ g.q^2≤M :=
    ⟨(hs g hg).1,(hs g hg).2,by rw [hdisp g hg]; exact (hs g hg).2⟩
  have hte := te_bounds d q M hM hs hdisp hqp
  let C := 2^N*(DebyeJetBounds.scale N b)^2
  let U := PhysicalReactionSeries.indexMajorant C q M (d.X-d.R) B 6
  have hU : Summable U := PhysicalReactionSeries.indexMajorant_summable C q M (d.X-d.R) B 6
    (by dsimp [C]; positivity) (zero_le_one.trans hB)
  have hbound (s : ℕ) (hsN : s≤N) (a : TotalIndex) (x : Space × Space) (hx : x∈ball (0 : Space × Space) b) :
      ‖iteratedFDeriv ℝ s (term d a i j) x‖≤2*U a := by
    rw [term,iteratedFDeriv_add_apply
      ((VectorReactionTerms.term_smooth true a i j d.gs d.R d.X d.hR).contDiffAt.of_le (by exact_mod_cast le_top))
      ((VectorReactionTerms.term_smooth false a i j (d.gs.map teLayer) d.R d.X d.hR).contDiffAt.of_le (by exact_mod_cast le_top))]
    have h1 := VectorReactionTerms.actual_joint_jet_bound true a i j d.chain q M (d.X-d.R) B
      hq hM0 hR hB ht hX le_rfl htm hqp N s hsN b hb.le hbB x (mem_ball_zero_iff.mp hx).le
    have h2 := VectorReactionTerms.actual_joint_jet_bound false a i j (te_chain d.chain) q M (d.X-d.R) B
      hq hM0 hR hB ht hX le_rfl hte.1 hte.2 N s hsN b hb.le hbB x (mem_ball_zero_iff.mp hx).le
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by
      dsimp [U,PhysicalReactionSeries.indexMajorant,C]
      ring))
  have hsum := LocalSmoothSeries.iteratedFDeriv_tsum_on_open (fun a => term d a i j)
    (fun a => term_smooth d a i j) N (ball 0 b) isOpen_ball
    (convex_ball (0 : Space × Space) b).isPreconnected 0 (mem_ball_self hb)
    (fun _ a => 2*U a) (fun _ _ => hU.mul_left 2) hbound m hm p (mem_ball_zero_iff.mpr hp)
  have hst := VectorReactionSeries.actual_derivative_summable true i j d.chain q M (d.X-d.R) B
    hq hM0 hR hB ht hX le_rfl htm hqp N m hm b hb.le hbB p hp.le
  have hse := VectorReactionSeries.actual_derivative_summable false i j (te_chain d.chain) q M (d.X-d.R) B
    hq hM0 hR hB ht hX le_rfl hte.1 hte.2 N m hm b hb.le hbB p hp.le
  change iteratedFDeriv ℝ m (fun z => ∑' a : TotalIndex,term d a i j z) p=_
  rw [hsum,
    VectorReactionSeries.actual_iteratedFDeriv_series true i j d.chain q M (d.X-d.R) B
      hq hM0 hR hB ht hX le_rfl htm hqp N m hm b hb hbB p hp,
    VectorReactionSeries.actual_iteratedFDeriv_series false i j (te_chain d.chain) q M (d.X-d.R) B
      hq hM0 hR hB ht hX le_rfl hte.1 hte.2 N m hm b hb hbB p hp,←hst.tsum_add hse]
  apply tsum_congr
  intro a
  exact iteratedFDeriv_add_apply
    ((VectorReactionTerms.term_smooth true a i j d.gs d.R d.X d.hR).contDiffAt.of_le (by exact_mod_cast le_top))
    ((VectorReactionTerms.term_smooth false a i j (d.gs.map teLayer) d.R d.X d.hR).contDiffAt.of_le (by exact_mod_cast le_top))

theorem kernel_jet_eq_series (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (b B T : ℝ) (hb : 0≤b) (hB : 0≤B) (hscale : degreeScale 2 b≤B)
    (hT : 2≤T) (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hTR : T<d.R) (hbR : b<d.R)
    (p : Space × Space) (hp : ‖p‖<b) (i j : Fin 3) (m : ℕ) :
    iteratedFDeriv ℝ m (kernel c d i j) p=iteratedFDeriv ℝ m (series d i j) p :=
  jet_eq_of_eventuallyEq _ _ p
    (kernel_eventually_series c d hm hdisp hu b B T hb hB hscale hT hBT hTR hbR p hp i j) m

end OQ14.SourceTensorJets
#print axioms OQ14.SourceTensorJets.jet_eq_of_eventuallyEq
#print axioms OQ14.SourceTensorJets.term_smooth
#print axioms OQ14.SourceTensorJets.te_bounds
#print axioms OQ14.SourceTensorJets.series_derivative
#print axioms OQ14.SourceTensorJets.kernel_jet_eq_series
