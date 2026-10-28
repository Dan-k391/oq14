import ConicalCommonRetention

/-! Tip-centered scalar coordinates of the common response converge to the original static cone. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalCommonTipConvergence
open MeasureTheory Set Metric Filter OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev VectorL2 := VectorFourier.VectorL2

theorem scalar_untranslate (c : Space) (F : FourierL2.ScalarL2) :
    StaticBallTranslation.scalar (-c) (StaticBallTranslation.scalar c F) = F := by
  apply Lp.ext
  have hs := (measurePreserving_add_right (volume : Measure Space) c).quasiMeasurePreserving.ae
    (StaticBallTranslation.scalar_ae c F)
  filter_upwards [StaticBallTranslation.scalar_ae (-c) (StaticBallTranslation.scalar c F), hs] with x hx hs
  rw [hx]
  simpa only [sub_neg_eq_add, neg_neg, sub_eq_add_neg, add_neg_cancel_right] using hs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def tipCoordinate (i : ι) (j : Fin 3) (R T k : ℝ) : FourierL2.ScalarL2 :=
  StaticBallTranslation.scalar (-center i)
    (physicalCoordinate (ConicalCommonDynamic.field p a center B hB hcontrast ha hsep i R T k) j)

omit [DecidableEq ι] in
theorem tipCoordinate_tendsto (i : ι) (j : Fin 3) (R T : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T) :
    Tendsto (tipCoordinate p a center B hB hcontrast ha hsep i j R T) (𝓝 0)
      (𝓝 (physicalCoordinate (ConicalStaticVolume.electric (p i)) j)) := by
  have ht := ((StaticBallTranslation.scalar (-center i)).continuous.tendsto _).comp
    (((DynamicConvolution.component j).continuous.tendsto _).comp
      (ConicalCommonDynamic.field_tendsto p a center B hB hcontrast ha hsep i R T hR hRT))
  change Tendsto (tipCoordinate p a center B hB hcontrast ha hsep i j R T) (𝓝 0)
    (𝓝 (StaticBallTranslation.scalar (-center i) (physicalCoordinate
      (ConicalCommonBaseline.electric p center i) j))) at ht
  rw [ConicalCommonBaseline.electric, ConicalCommonBaseline.translate_coordinate, scalar_untranslate] at ht
  exact ht

def tipPair (i : ι) (R T k : ℝ) (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hc : HasCompactSupport ζ) : ℂ :=
  ∑ j : Fin 3, WeakGreen.scalarProduct (ConicalAnnularCoefficient.testCoordinate (p i) ζ hζ hc j)
    (tipCoordinate p a center B hB hcontrast ha hsep i j R T k)

omit [DecidableEq ι] in
theorem tipPair_tendsto (i : ι) (R T : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ) :
    Tendsto (fun k => tipPair p a center B hB hcontrast ha hsep i R T k ζ hζ hc) (𝓝 0)
      (𝓝 (ConicalAnnularCoefficient.fieldPair (p i) ζ hζ hc (ConicalStaticVolume.electric (p i)))) := by
  rw [ConicalAnnularCoefficient.fieldPair_apply]
  apply tendsto_finset_sum
  intro j hj
  exact ((WeakGreen.scalarProduct (ConicalAnnularCoefficient.testCoordinate (p i) ζ hζ hc j)).continuous.tendsto _).comp
    (tipCoordinate_tendsto p a center B hB hcontrast ha hsep i j R T hR hRT)

end OQ14.ConicalCommonTipConvergence
#print axioms OQ14.ConicalCommonTipConvergence.scalar_untranslate
#print axioms OQ14.ConicalCommonTipConvergence.tipCoordinate_tendsto
#print axioms OQ14.ConicalCommonTipConvergence.tipPair_tendsto
