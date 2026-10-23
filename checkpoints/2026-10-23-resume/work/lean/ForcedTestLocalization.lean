import ForcedMaxwellResponse
import WeakPoynting.InteriorTestDensity

/-! Global source equations obtained by actual smooth-test localization near one point. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ForcedTestLocalization
open MeasureTheory Filter Set OQ14.Maxwell OQ14.MaterialMaxwell OQ14.MagneticResponse
  OQ14.DynamicSource OQ14.ForcedMaxwellResponse
open scoped Topology

def Equation (k : ℝ) (ρ : Fin 3 → Space → ℂ) (E H : Field) (f : Test) : Prop :=
  ∀ i : Fin 3,
    curlPair (fieldPair E) i f=Complex.I*(k : ℂ)*fieldPair H i f ∧
    curlPair (fieldPair H) i f= -(Complex.I*(k : ℂ))*(fieldPair E i f+∫ x,ρ i x*f.val x)

theorem scalar_pair_split (u : Space → ℂ) (hu : LocallyIntegrable u) (f g h : Test)
    (hs : ∀ x, f.val x=g.val x+h.val x) :
    (∫ x,u x*f.val x)=(∫ x,u x*g.val x)+(∫ x,u x*h.val x) := by
  simp_rw [hs,mul_add]
  exact integral_add
    (PointSingularity.test_product_integrable _ _ hu g.val.continuous g.property)
    (PointSingularity.test_product_integrable _ _ hu h.val.continuous h.property)

theorem partial_split (f g h : Test) (hs : ∀ x, f.val x=g.val x+h.val x) (i : Fin 3) (x : Space) :
    (testPartial i f).val x=(testPartial i g).val x+(testPartial i h).val x := by
  change dcoord (f.val : Space → ℂ) x i=dcoord (g.val : Space → ℂ) x i+dcoord (h.val : Space → ℂ) x i
  rw [show (f.val : Space → ℂ)=(fun y => g.val y+h.val y) from funext hs]
  exact partial_add ((g.val.smooth 1).differentiable (by norm_num) x)
    ((h.val.smooth 1).differentiable (by norm_num) x) i

theorem curl_pair_split (E : Field) (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (f g h : Test) (hs : ∀ x, f.val x=g.val x+h.val x) (i : Fin 3) :
    curlPair (fieldPair E) i f=curlPair (fieldPair E) i g+curlPair (fieldPair E) i h := by
  unfold curlPair fieldPair
  rw [scalar_pair_split _ (hE _) _ _ _ (partial_split f g h hs _),
    scalar_pair_split _ (hE _) _ _ _ (partial_split f g h hs _)]
  ring

theorem equation_split (k : ℝ) (ρ : Fin 3 → Space → ℂ) (E H : Field)
    (hρ : ∀ i, LocallyIntegrable (ρ i))
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (f g h : Test) (hs : ∀ x, f.val x=g.val x+h.val x)
    (hg : Equation k ρ E H g) (hh : Equation k ρ E H h) : Equation k ρ E H f := by
  intro i
  have he : fieldPair E i f=fieldPair E i g+fieldPair E i h := scalar_pair_split _ (hE i) f g h hs
  have hm : fieldPair H i f=fieldPair H i g+fieldPair H i h := scalar_pair_split _ (hH i) f g h hs
  have hr := scalar_pair_split (ρ i) (hρ i) f g h hs
  constructor
  · rw [curl_pair_split E hE f g h hs i,(hg i).1,(hh i).1,hm]
    ring
  · rw [curl_pair_split H hH f g h hs i,(hg i).2,(hh i).2,he,hr]
    ring

theorem of_near_and_punctured (k : ℝ) (ρ : Fin 3 → Space → ℂ) (E H : Field)
    (hρ : ∀ i, LocallyIntegrable (ρ i))
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (Ω : Set Space) (hΩ : IsOpen Ω) (h0 : (0 : Space)∈Ω)
    (hnear : ∀ f : Test, tsupport (f.val : Space → ℂ) ⊆ Ω → Equation k ρ E H f)
    (hpunctured : ∀ f : Test, (0 : Space)∉tsupport (f.val : Space → ℂ) → Equation k ρ E H f) :
    TestForced k ρ E H := by
  obtain ⟨χ,hχ⟩ := InteriorTestDensity.exists_smooth_interior hΩ isCompact_singleton
    (show ({0} : Set Space) ⊆ Ω from singleton_subset_iff.mpr h0)
  have hχ0 := hχ 0 (mem_singleton 0)
  intro i f
  let g : Test := ⟨InteriorTestDensity.cutSchwartz χ f.val,χ.compact.mul_right⟩
  have hcompact : HasCompactSupport (fun x => f.val x-g.val x) :=
    f.property.comp₂_left g.property (show (0 : ℂ)-0=0 from sub_self 0)
  let h : Test := ⟨FourierL2.compactSmoothSchwartz
    (fun x => f.val x-g.val x) ((f.val.smooth (⊤ : ℕ∞)).sub (g.val.smooth (⊤ : ℕ∞)))
    hcompact,hcompact⟩
  have hsplit (x : Space) : f.val x=g.val x+h.val x := by
    change f.val x=g.val x+(f.val x-g.val x)
    ring
  have hg : tsupport (g.val : Space → ℂ) ⊆ Ω :=
    (tsupport_mul_subset_left (f := χ.function) (g := (f.val : Space → ℂ))).trans χ.inside
  have hh : (0 : Space)∉tsupport (h.val : Space → ℂ) := by
    apply not_mem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [hχ0] with x hx
    change f.val x-χ.function x*f.val x=0
    rw [hx,one_mul,sub_self]
  exact equation_split k ρ E H hρ hE hH f g h hsplit (hnear g hg) (hpunctured h hh) i

end OQ14.ForcedTestLocalization
#print axioms OQ14.ForcedTestLocalization.scalar_pair_split
#print axioms OQ14.ForcedTestLocalization.partial_split
#print axioms OQ14.ForcedTestLocalization.curl_pair_split
#print axioms OQ14.ForcedTestLocalization.equation_split
#print axioms OQ14.ForcedTestLocalization.of_near_and_punctured
