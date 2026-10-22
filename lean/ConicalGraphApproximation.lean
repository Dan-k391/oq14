import ConicalSchwartzLocalization
import WeakPoynting.InteriorTestDensity

/-! Actual L2 weak derivatives and common-support smoothing of conical tests. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalGraphApproximation
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.ConicalCutoffGradient
  OQ14.ConicalComplexLocalization OQ14.ConicalSchwartzLocalization
  OQ14.DivCurlCompact OQ14.PartialSmoothing OQ14.InteriorTestDensity OQ14.WeakGreen Filter
open scoped Topology SchwartzMap

def potentialL2 (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) : L2Scalar :=
  (cutPotential_memLp_complex χ ν a t hν ha ht ht1).toLp (fun x => (cutPotential χ ν a t x : ℂ))

def electricL2 (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) : L2Scalar :=
  (cutElectric_memLp_complex χ ν a t hν ha ht ht1 i).toLp (fun x => complexify (cutElectric χ ν a t) x i)

theorem potentialL2_ae (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    (potentialL2 χ ν a t hν ha ht ht1 : Space → ℂ) =ᵐ[volume] fun x => (cutPotential χ ν a t x : ℂ) :=
  (cutPotential_memLp_complex χ ν a t hν ha ht ht1).coeFn_toLp

theorem electricL2_ae (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    (electricL2 χ ν a t hν ha ht ht1 i : Space → ℂ) =ᵐ[volume] fun x => complexify (cutElectric χ ν a t) x i :=
  (cutElectric_memLp_complex χ ν a t hν ha ht ht1 i).coeFn_toLp

theorem potential_compact (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    CompactRepresentative (potentialL2 χ ν a t hν ha ht ht1) := by
  refine ⟨_, ?_, potentialL2_ae χ ν a t hν ha ht ht1⟩
  exact (χ.hasCompactSupport.mul_right (f' := ConicalCapField.potential ν a t)).comp_left
    (g := Complex.ofReal) (by simp)

theorem potential_hasWeakPartial (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    HasWeakPartial (potentialL2 χ ν a t hν.le ha ht ht1) (electricL2 χ ν a t hν.le ha ht ht1 i) i := by
  apply hasWeakPartial_of_schwartz_integral i
  intro ψ
  have hE : (∫ x : Space, electricL2 χ ν a t hν.le ha ht ht1 i x*ψ x)=
      ∫ x : Space, complexify (cutElectric χ ν a t) x i*ψ x := by
    apply integral_congr_ae
    filter_upwards [electricL2_ae χ ν a t hν.le ha ht ht1 i] with x hx
    rw [hx]
  have hU : (∫ x : Space, potentialL2 χ ν a t hν.le ha ht ht1 x*dcoord ψ x i)=
      ∫ x : Space, (cutPotential χ ν a t x : ℂ)*dcoord ψ x i := by
    apply integral_congr_ae
    filter_upwards [potentialL2_ae χ ν a t hν.le ha ht ht1] with x hx
    rw [hx]
  rw [hE,hU]
  have h := cut_weak_partial_schwartz χ ν a t hν ha ht ht1 i ψ
  simpa only [GradientProjection.pderivative_apply,neg_add_cancel] using congrArg
    (fun z : ℂ => z+(∫ x : Space, (cutPotential χ ν a t x : ℂ)*dcoord ψ x i)) h

theorem conical_graph_approximation (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    ∃ f : ℕ → 𝓢(Space, ℂ),
      Tendsto (fun n => FourierL2.embed (f n)) atTop (𝓝 (potentialL2 χ ν a t hν.le ha ht ht1)) ∧
      ∀ i, Tendsto (fun n => FourierL2.embed (GradientProjection.pderivative i (f n))) atTop
        (𝓝 (electricL2 χ ν a t hν.le ha ht ht1 i)) :=
  compact_partial_graph_approximation (potential_compact χ ν a t hν.le ha ht ht1)
    (potential_hasWeakPartial χ ν a t hν ha ht ht1)

def multipliedDerivative {Ω : Set Space} (κ : SmoothInterior Ω) (u : L2Scalar)
    (D : Fin 3 → L2Scalar) (i : Fin 3) : L2Scalar :=
  scaleL2 κ.function κ.regular.continuous κ.compact (D i)+
    scaleL2 (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
      (κ.compact.fderiv_apply ℝ (basis i)) u

theorem multipliedDerivative_ae {Ω : Set Space} (κ : SmoothInterior Ω) (u : L2Scalar)
    (D : Fin 3 → L2Scalar) (i : Fin 3) :
    (multipliedDerivative κ u D i : Space → ℂ) =ᵐ[volume]
      fun x => κ.function x*D i x+dcoord κ.function x i*u x := by
  filter_upwards [scaleL2_ae κ.function κ.regular.continuous κ.compact (D i),
    scaleL2_ae (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
      (κ.compact.fderiv_apply ℝ (basis i)) u,
    Lp.coeFn_add (scaleL2 κ.function κ.regular.continuous κ.compact (D i))
      (scaleL2 (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
        (κ.compact.fderiv_apply ℝ (basis i)) u)] with x hv hd ha
  change (scaleL2 κ.function κ.regular.continuous κ.compact (D i)+
    scaleL2 (fun x => dcoord κ.function x i) (partial_continuous κ.regular i)
      (κ.compact.fderiv_apply ℝ (basis i)) u) x=_
  rw [ha]
  simp only [Pi.add_apply,hv,hd]

theorem localized_graph_approximation {Ω : Set Space} (κ : SmoothInterior Ω)
    {u : L2Scalar} {D : Fin 3 → L2Scalar} (hu : CompactRepresentative u)
    (hD : ∀ i, HasWeakPartial u (D i) i) :
    ∃ f : ℕ → 𝓢(Space, ℂ),
      (∀ n, tsupport (f n : Space → ℂ) ⊆ tsupport κ.function) ∧
      Tendsto (fun n => FourierL2.embed (f n)) atTop
        (𝓝 (scaleL2 κ.function κ.regular.continuous κ.compact u)) ∧
      ∀ i, Tendsto (fun n => FourierL2.embed (GradientProjection.pderivative i (f n))) atTop
        (𝓝 (multipliedDerivative κ u D i)) := by
  obtain ⟨g,hg,hgd⟩ := compact_partial_graph_approximation hu hD
  refine ⟨fun n => cutSchwartz κ (g n),fun n => cutSchwartz_support κ (g n),?_,?_⟩
  · simpa only [embed_cutSchwartz] using
      ((scaleL2_continuous κ.function κ.regular.continuous κ.compact).tendsto _ |>.comp hg)
  · intro i
    have hv := (scaleL2_continuous κ.function κ.regular.continuous κ.compact).tendsto _ |>.comp (hgd i)
    have hd := (scaleL2_continuous (fun x => dcoord κ.function x i)
      (partial_continuous κ.regular i) (κ.compact.fderiv_apply ℝ (basis i))).tendsto _ |>.comp hg
    simpa only [embed_partial_cutSchwartz,multipliedDerivative] using hv.add hd

theorem localized_hasWeakPartial {Ω : Set Space} (κ : SmoothInterior Ω)
    {u : L2Scalar} {D : Fin 3 → L2Scalar} (hu : CompactRepresentative u)
    (hD : ∀ i, HasWeakPartial u (D i) i) (i : Fin 3) :
    HasWeakPartial (scaleL2 κ.function κ.regular.continuous κ.compact u)
      (multipliedDerivative κ u D i) i := by
  obtain ⟨f,_,hf,hdf⟩ := localized_graph_approximation κ hu hD
  exact weakPartial_limit i hf (hdf i) (fun n => schwartz_hasWeakPartial (f n) i)

end OQ14.ConicalGraphApproximation

#print axioms OQ14.ConicalGraphApproximation.potentialL2_ae
#print axioms OQ14.ConicalGraphApproximation.electricL2_ae
#print axioms OQ14.ConicalGraphApproximation.potential_compact
#print axioms OQ14.ConicalGraphApproximation.potential_hasWeakPartial
#print axioms OQ14.ConicalGraphApproximation.conical_graph_approximation
#print axioms OQ14.ConicalGraphApproximation.multipliedDerivative_ae
#print axioms OQ14.ConicalGraphApproximation.localized_graph_approximation
#print axioms OQ14.ConicalGraphApproximation.localized_hasWeakPartial
