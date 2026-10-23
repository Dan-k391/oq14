import SourceLocalBounds
import MaterialMaxwell

/-! Literal nonnegative susceptibility of an actual finite radial material stack. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceMaterialCoefficient
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem

def realSigma (d : Data) (r : ℝ) : ℝ :=
  if r≤d.R then 1 else if r≤d.X then RadialGluing.sigmaAt d.gs r else 1

theorem sigma_eq (d : Data) (r : ℝ) : sigma d r=(realSigma d r : ℂ) := by
  unfold sigma SourceRadialSystem.extend realSigma
  split_ifs <;> rfl

theorem sigmaAt_bounds {gs : List RadialStack.Layer} {X R M : ℝ}
    (h : RadialStack.Chain gs X R)
    (hs : ∀ g∈gs, 1≤g.σ ∧ g.σ≤M) (r : ℝ) (hr : R<r) (hx : r≤X) :
    1≤RadialGluing.sigmaAt gs r ∧ RadialGluing.sigmaAt gs r≤M := by
  induction h with
  | nil R => exact False.elim (not_lt_of_ge hx hr)
  | cons g gs R h ih =>
    by_cases hg : g.a<r
    · simpa only [RadialGluing.sigmaAt,if_pos hg] using hs g (by simp)
    · simp only [RadialGluing.sigmaAt,if_neg hg]
      exact ih (fun a ha => hs a (by simp [ha])) hr (le_of_not_gt hg)

theorem realSigma_bounds (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs, 1≤g.σ ∧ g.σ≤M) (r : ℝ) :
    1≤realSigma d r ∧ realSigma d r≤M := by
  unfold realSigma
  split_ifs with hr hx
  · exact ⟨le_rfl,hM⟩
  · exact sigmaAt_bounds d.chain hs r (lt_of_not_ge hr) hx
  · exact ⟨le_rfl,hM⟩

theorem realSigma_measurable (d : Data) : Measurable (realSigma d) := by
  have he : realSigma d=(fun r => (sigma d r).re) := by
    funext r
    rw [sigma_eq]
    rfl
  rw [he]
  exact Complex.continuous_re.measurable.comp (SourceLocalBounds.sigma_measurable d)

def susceptibility (d : Data) (x : Space) : ℝ := realSigma d ‖x‖-1

theorem susceptibility_measurable (d : Data) : Measurable (susceptibility d) :=
  ((realSigma_measurable d).comp continuous_norm.measurable).sub measurable_const

def coefficient (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs, 1≤g.σ ∧ g.σ≤M) : StaticCoefficient.Coefficient where
  value ξ := susceptibility d (VectorFourier.coordinateMap.symm ξ)
  bound := M-1
  measurable := (susceptibility_measurable d).comp VectorFourier.coordinateMap.symm.measurable
  nonnegative _ :=  sub_nonneg.mpr (realSigma_bounds d M hM hs _).1
  bounded _ :=  sub_le_sub_right (realSigma_bounds d M hM hs _).2 1

theorem value_physical (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs, 1≤g.σ ∧ g.σ≤M) (x : Space) :
    (coefficient d M hM hs).value (VectorFourier.coordinateMap x)=susceptibility d x := by
  simp only [coefficient,VectorFourier.coordinateMap.symm_apply_apply]

theorem value_complex (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs, 1≤g.σ ∧ g.σ≤M) (x : Space) :
    ((coefficient d M hM hs).value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1 := by
  rw [value_physical,sigma_eq]
  simp only [susceptibility,Complex.ofReal_sub,Complex.ofReal_one]

theorem value_inner (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs, 1≤g.σ ∧ g.σ≤M) (x : Space) (hx : ‖x‖≤d.R) :
    (coefficient d M hM hs).value (VectorFourier.coordinateMap x)=0 := by
  rw [value_physical]
  simp only [susceptibility,realSigma,if_pos hx,sub_self]

theorem value_outer (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs, 1≤g.σ ∧ g.σ≤M) (x : Space) (hx : d.X<‖x‖) :
    (coefficient d M hM hs).value (VectorFourier.coordinateMap x)=0 := by
  have hr := (RadialStack.chain_ordered d.chain).trans_lt hx
  rw [value_physical]
  simp only [susceptibility,realSigma,if_neg (not_le.mpr hr),if_neg (not_le.mpr hx),sub_self]

theorem dielectric_eq (d : Data) (M : ℝ) (hM : 1≤M)
    (hs : ∀ g∈d.gs, 1≤g.σ ∧ g.σ≤M) (x : Space) :
    MaterialMaxwell.dielectric (coefficient d M hM hs) x=realSigma d ‖x‖ := by
  rw [MaterialMaxwell.dielectric,value_physical]
  unfold susceptibility
  ring

end OQ14.SourceMaterialCoefficient

#print axioms OQ14.SourceMaterialCoefficient.sigma_eq
#print axioms OQ14.SourceMaterialCoefficient.sigmaAt_bounds
#print axioms OQ14.SourceMaterialCoefficient.realSigma_bounds
#print axioms OQ14.SourceMaterialCoefficient.realSigma_measurable
#print axioms OQ14.SourceMaterialCoefficient.susceptibility_measurable
#print axioms OQ14.SourceMaterialCoefficient.value_physical
#print axioms OQ14.SourceMaterialCoefficient.value_complex
#print axioms OQ14.SourceMaterialCoefficient.value_inner
#print axioms OQ14.SourceMaterialCoefficient.value_outer
#print axioms OQ14.SourceMaterialCoefficient.dielectric_eq
