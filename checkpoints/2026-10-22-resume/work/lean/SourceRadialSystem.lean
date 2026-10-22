import LayerMagneticMaxwell

/-! The normalized outgoing source state on the entire punctured radial domain. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.SourceRadialSystem
open MeasureTheory Set Filter OQ14.Maxwell OQ14.RadialStack OQ14.RadialGluing
  OQ14.ClippedLayerProfiles
open scoped Topology

structure Data where
  l : ℕ
  gs : List Layer
  R : ℝ
  X : ℝ
  c : ℝ
  hR : 0<R
  hc : 0<c
  chain : Chain gs X R

def extend (R X : ℝ) (f g : ℝ → ℂ) (r : ℝ) : ℂ :=
  if r≤R then g r else if r≤X then f r else g r

def raw (d : Data) : ℝ → State := sourceState d.l d.gs d.R d.X d.hR
def state (d : Data) (r : ℝ) : State := raw d (radius d.c r)
def sigma (d : Data) : ℝ → ℂ := extend d.R d.X (fun r => (sigmaAt d.gs r : ℂ)) (fun _ => 1)
def inverseSigma (d : Data) : ℝ → ℂ := extend d.R d.X (ClippedLayerProfiles.inverseSigma d.gs) (fun _ => 1)
def potential (d : Data) : ℝ → ℂ := extend d.R d.X (ClippedLayerProfiles.potential d.l d.gs)
  (fun r => (-HankelEnergy.weight d.l r : ℂ))
def interfaces (d : Data) : Set ℝ := {d.c,d.R,d.X} ∪ {r | r∈cuts d.gs}

theorem interfaces_countable (d : Data) : (interfaces d).Countable := by
  have he : {r : ℝ | r∈cuts d.gs}=(cuts d.gs).toFinset := by ext r; simp
  exact (Set.toFinite {d.c,d.R,d.X}).countable.union
    (he ▸ (cuts d.gs).toFinset.finite_toSet.countable)

theorem off_interfaces (d : Data) {r : ℝ} (hr : r∉(interfaces d)) :
    r≠d.c ∧ r≠d.R ∧ r≠d.X ∧ r∉cuts d.gs := by
  simpa only [interfaces,mem_union,mem_insert_iff,mem_singleton_iff,mem_setOf_eq,not_or,and_assoc] using hr

theorem state_continuous (d : Data) : Continuous (state d) := by
  apply (sourceState_continuousOn d.l d.chain d.hR).comp_continuous (radius_continuous d.c)
  intro r
  exact radius_pos d.c r d.hc

theorem raw_ode (d : Data) (r : ℝ) (hr : 0<r) (hi : r∉(interfaces d)) :
    HasDerivAt (fun t => ((raw d) t).1) ((sigma d) r*((raw d) r).2) r ∧
    HasDerivAt (fun t => ((raw d) t).2) ((potential d) r*((raw d) r).1) r := by
  obtain ⟨_,hR,hX,hcut⟩ := off_interfaces d hi
  rcases lt_or_gt_of_ne hR with hlt|hgt
  · simpa only [raw,sigma,potential,extend,if_pos hlt.le,one_mul] using
      sourceState_core_ode d.l d.gs d.R d.X d.hR r ⟨hr,hlt⟩
  · rcases lt_or_gt_of_ne hX with hlt|hXgt
    · simpa only [raw,sigma,potential,extend,if_neg (not_le.mpr hgt),if_pos hlt.le,
        ClippedLayerProfiles.potential_eq] using
        sourceState_stack_ode d.l d.gs d.R d.X d.hR r ⟨hgt,hlt⟩ hcut
    · simpa only [raw,sigma,potential,extend,if_neg (not_le.mpr hgt),if_neg (not_le.mpr hXgt),one_mul] using
        sourceState_exterior_ode d.l d.chain d.hR r hXgt

theorem extend_continuousAt (R X : ℝ) (f g : ℝ → ℂ) (r : ℝ)
    (hR : r≠R) (hX : r≠X) (hf : ContinuousAt f r) (hg : ContinuousAt g r) :
    ContinuousAt (extend R X f g) r := by
  rcases lt_or_gt_of_ne hR with hlt|hgt
  · apply hg.congr
    filter_upwards [Iio_mem_nhds hlt] with t ht
    simp only [extend,if_pos (show t≤R from le_of_lt ht)]
  · rcases lt_or_gt_of_ne hX with hlt|hXgt
    · apply hf.congr
      filter_upwards [Ioo_mem_nhds hgt hlt] with t ht
      simp only [extend,if_neg (not_le.mpr ht.1),if_pos ht.2.le]
    · apply hg.congr
      filter_upwards [Ioi_mem_nhds hgt,Ioi_mem_nhds hXgt] with t ht htX
      simp only [extend,if_neg (not_le.mpr (show R<t from ht)),if_neg (not_le.mpr (show X<t from htX))]

theorem inverseSigma_continuousAt (d : Data) (r : ℝ) (hi : r∉(interfaces d)) :
    ContinuousAt (inverseSigma d) r := by
  obtain ⟨_,hR,hX,hcut⟩ := off_interfaces d hi
  exact extend_continuousAt d.R d.X _ _ r hR hX
    (ClippedLayerProfiles.inverseSigma_continuousAt d.gs r hcut) continuousAt_const

theorem extend_measurable (R X : ℝ) (f g : ℝ → ℂ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (extend R X f g) :=
  hg.ite (measurableSet_le measurable_id measurable_const)
    (hf.ite (measurableSet_le measurable_id measurable_const) hg)

theorem inverseSigma_measurable (d : Data) : Measurable (inverseSigma d) :=
  extend_measurable d.R d.X _ _ (ClippedLayerProfiles.inverseSigma_measurable d.gs) measurable_const

theorem locallyIntegrable_ite {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) (s : Set Y) [DecidablePred (·∈s)] (hs : MeasurableSet s)
    (f g : Y → ℂ) (hf : LocallyIntegrable f μ) (hg : LocallyIntegrable g μ) :
    LocallyIntegrable (s.piecewise f g) μ := by
  have he : s.piecewise f g=s.indicator f+sᶜ.indicator g := by
    ext x
    by_cases hx : x∈s <;> simp [Set.piecewise,Set.indicator,hx]
  rw [he]
  exact (hf.indicator hs).add (hg.indicator hs.compl)

theorem extend_locallyIntegrable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) (R X : ℝ) (f g : ℝ → ℂ) (ρ : Y → ℝ) (hρ : Measurable ρ)
    (hf : LocallyIntegrable (fun x => f (ρ x)) μ)
    (hg : LocallyIntegrable (fun x => g (ρ x)) μ) :
    LocallyIntegrable (fun x => extend R X f g (ρ x)) μ := by
  exact locallyIntegrable_ite μ {x | ρ x≤R} (measurableSet_le hρ measurable_const) _ _ hg
    (locallyIntegrable_ite μ {x | ρ x≤X} (measurableSet_le hρ measurable_const) _ _ hf hg)

theorem inverseSigma_locallyIntegrable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] (μ : Measure Y) [IsLocallyFiniteMeasure μ] (d : Data) (ρ : Y → ℝ) (hρ : Measurable ρ) :
    LocallyIntegrable (fun x => (inverseSigma d) (ρ x)) μ := by
  apply extend_locallyIntegrable μ d.R d.X _ _ ρ hρ
  · exact select_comp_locallyIntegrable μ d.gs _ _ ρ hρ
      (fun _ => continuous_const.locallyIntegrable) continuous_const.locallyIntegrable
  · exact continuous_const.locallyIntegrable

theorem sigma_locallyIntegrable (d : Data) (ρ : Space → ℝ) (hρ : Measurable ρ) :
    LocallyIntegrable (fun x => (sigma d) (ρ x)) := by
  apply extend_locallyIntegrable volume d.R d.X _ _ ρ hρ
  · simp_rw [LayerMagneticProfiles.sigma_select]
    exact select_comp_locallyIntegrable volume d.gs _ _ ρ hρ
      (fun _ => continuous_const.locallyIntegrable) continuous_const.locallyIntegrable
  · exact continuous_const.locallyIntegrable

theorem potential_locallyIntegrable (d : Data) (ρ : Space → ℝ) (hρ : Continuous ρ) :
    LocallyIntegrable (fun x => (potential d) (radius d.c (ρ x))) := by
  apply extend_locallyIntegrable volume d.R d.X _ _ _ ((radius_continuous d.c).comp hρ).measurable
  · exact potential_comp_locallyIntegrable d.l d.gs d.c d.hc ρ hρ
  · have hh : Continuous (fun r => (-HankelEnergy.weight d.l (radius d.c r) : ℂ)) := by
      unfold HankelEnergy.weight
      apply Continuous.neg
      apply Complex.continuous_ofReal.comp
      exact continuous_const.sub (continuous_const.div ((radius_continuous d.c).pow 2)
        (fun r => pow_ne_zero 2 (radius_pos d.c r d.hc).ne'))
    exact (hh.comp hρ).locallyIntegrable

theorem dispersion_identity (d : Data) (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (r : ℝ) :
    (inverseSigma d) r*((d.l : ℂ)*(d.l+1)/(r : ℂ)^2)-(potential d) r=1 := by
  by_cases hR : r≤d.R
  · simp only [inverseSigma,potential,extend,if_pos hR,HankelEnergy.weight,HankelEnergy.angular,
      Complex.ofReal_neg,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_pow,
      Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_add,Complex.ofReal_one]
    ring
  · by_cases hX : r≤d.X
    · simpa only [inverseSigma,potential,extend,if_neg hR,if_pos hX,Complex.ofReal_one,one_pow] using
        LayerElectricMaxwell.dispersion_identity d.l d.chain 1
          (by intro g hg; simpa using hdisp g hg) r (not_le.mp hR) hX
    · simp only [inverseSigma,potential,extend,if_neg hR,if_neg hX,HankelEnergy.weight,HankelEnergy.angular,
        Complex.ofReal_neg,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_pow,
        Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_add,Complex.ofReal_one]
      ring

end OQ14.SourceRadialSystem

#print axioms OQ14.SourceRadialSystem.interfaces_countable
#print axioms OQ14.SourceRadialSystem.off_interfaces
#print axioms OQ14.SourceRadialSystem.state_continuous
#print axioms OQ14.SourceRadialSystem.raw_ode
#print axioms OQ14.SourceRadialSystem.extend_continuousAt
#print axioms OQ14.SourceRadialSystem.inverseSigma_continuousAt
#print axioms OQ14.SourceRadialSystem.extend_measurable
#print axioms OQ14.SourceRadialSystem.inverseSigma_measurable
#print axioms OQ14.SourceRadialSystem.locallyIntegrable_ite
#print axioms OQ14.SourceRadialSystem.extend_locallyIntegrable
#print axioms OQ14.SourceRadialSystem.inverseSigma_locallyIntegrable
#print axioms OQ14.SourceRadialSystem.sigma_locallyIntegrable
#print axioms OQ14.SourceRadialSystem.potential_locallyIntegrable
#print axioms OQ14.SourceRadialSystem.dispersion_identity
