import ConicalIntrinsicCoefficient
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual finite-angular incident fields give intrinsic linear conical coefficient functionals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.ConicalAngularCoefficient
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
open scoped Topology
abbrev Space := Maxwell.Space
abbrev ModeIndex := ComplexTransverseExpansion.ModeIndex
abbrev Input := ModeIndex →₀ ℂ

def angularLinear : Input →ₗ[ℂ] ComplexVectorSphere.Ambient :=
  Finsupp.linearCombination ℂ ComplexTransverseExpansion.vector

theorem incident_add (k : ℝ) (c d : Input) (x : Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident k (c+d)).E x i=
      (FiniteAngularHerglotz.incident k c).E x i+(FiniteAngularHerglotz.incident k d).E x i := by
  simp only [FiniteAngularHerglotz.electric_value]
  change HerglotzAngularL2.value k x i (angularLinear (c+d))=_
  rw [map_add,map_add]
  rfl

theorem restricted_add (a k : ℝ) (c d : Input) :
    ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k (c+d))=
      ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c)+
        ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k d) := by
  apply PiLp.ext
  intro i
  apply Lp.ext
  filter_upwards [ConicalEntireGauge.restricted_ae a (FiniteAngularHerglotz.incident k (c+d)) i,
    Lp.coeFn_add (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c) i)
      (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k d) i),
    ConicalEntireGauge.restricted_ae a (FiniteAngularHerglotz.incident k c) i,
    ConicalEntireGauge.restricted_ae a (FiniteAngularHerglotz.incident k d) i] with x he ha hc hd
  change (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k (c+d)) i : Space → ℂ) x=
    (ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c) i+ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k d) i : ConicalRungeBall.ScalarBall a) x
  rw [he,ha]
  simp only [Pi.add_apply,hc,hd,incident_add]

def restrictedLinear (a k : ℝ) : Input →ₗ[ℂ] ConicalRungeBall.BallL2 a where
  toFun c := ConicalEntireGauge.restricted a (FiniteAngularHerglotz.incident k c)
  map_add' := restricted_add a k
  map_smul' z c := ConicalNormalizedInputTransfer.restricted_smul a k z c

section Device
variable (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
  (hai : a < p.cutoff.rIn) (hba : b < a) (hk : k≠0)
  (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
  (hν : p.exponent < 1)

def extension (c : Input) : Field := Classical.choose
  (ConicalEntireGauge.exists_incident_extension p a b k hai hba (FiniteAngularHerglotz.incident k c))

theorem extension_continuous (c : Input) (i : Fin 3) :
    Continuous (fun x => extension p a b k hai hba c x i) :=
  ((Classical.choose_spec (ConicalEntireGauge.exists_incident_extension p a b k hai hba
    (FiniteAngularHerglotz.incident k c))).1 i).continuous

theorem extension_eq (c : Input) (i : Fin 3) (x : Space) (hx : x ∈ closedBall (0 : Space) b) :
    extension p a b k hai hba c x i=ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k c) i x :=
  (Classical.choose_spec (ConicalEntireGauge.exists_incident_extension p a b k hai hba
    (FiniteAngularHerglotz.incident k c))).2.2 i x hx

def system (c : Input) : System p b :=
  ConicalEntireGauge.system p a b k ha hai hba hk hfreq (FiniteAngularHerglotz.incident k c)
    (extension p a b k hai hba c) (extension_continuous p a b k hai hba c) (extension_eq p a b k hai hba c)

def fieldLinear : Input →ₗ[ℂ] ConicalRungeBall.BallL2 a :=
  (ConicalInputCoefficient.fieldOperator p a a k).toLinearMap.comp (restrictedLinear a k)

theorem system_total_ae (c : Input) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate (system p a b k ha hai hba hk hfreq c) i x=fieldLinear p a k c i x := by
  filter_upwards [ConicalEntireGauge.system_total_inner p a b k ha hai hba hk hfreq
    (FiniteAngularHerglotz.incident k c) _ _ (extension_eq p a b k hai hba c) i,
    (ae_restrict_iff' measurableSet_closedBall).mp
      (ConicalEntireStability.field_ae p a a k le_rfl (FiniteAngularHerglotz.incident k c) i)] with x ht hf hx
  exact (ht hx).trans (hf ((ball_subset_ball hba.le).trans ball_subset_closedBall hx)).symm

def coefficient (c : Input) : ℂ :=
  ConicalIntrinsicCoefficient.coefficient (system p a b k ha hai hba hk hfreq c) hb (hba.trans hai) hν

theorem coefficient_add (c d : Input) :
    coefficient p a b k ha hb hai hba hk hfreq hν (c+d)=
      coefficient p a b k ha hb hai hba hk hfreq hν c+coefficient p a b k ha hb hai hba hk hfreq hν d := by
  apply ConicalIntrinsicCoefficient.coefficient_add _ _ _ hb (hba.trans hai) hν
  intro i
  have hl : fieldLinear p a k (c+d)=fieldLinear p a k c+fieldLinear p a k d := map_add _ _ _
  filter_upwards [system_total_ae p a b k ha hai hba hk hfreq (c+d) i,
    system_total_ae p a b k ha hai hba hk hfreq c i,system_total_ae p a b k ha hai hba hk hfreq d i,
    (ae_restrict_iff' measurableSet_closedBall).mp (Lp.coeFn_add (fieldLinear p a k c i) (fieldLinear p a k d i))]
    with x hcd hc hd hadd hx
  rw [hcd hx,hc hx,hd hx,hl]
  exact hadd ((ball_subset_ball hba.le).trans ball_subset_closedBall hx)

theorem coefficient_smul (z : ℂ) (c : Input) :
    coefficient p a b k ha hb hai hba hk hfreq hν (z • c)=z*coefficient p a b k ha hb hai hba hk hfreq hν c := by
  apply ConicalIntrinsicCoefficient.coefficient_scaled _ _ hb (hba.trans hai) hν z
  intro i
  have hl : fieldLinear p a k (z • c)=z • fieldLinear p a k c := map_smul _ _ _
  filter_upwards [system_total_ae p a b k ha hai hba hk hfreq (z • c) i,
    system_total_ae p a b k ha hai hba hk hfreq c i,
    (ae_restrict_iff' measurableSet_closedBall).mp (Lp.coeFn_smul z (fieldLinear p a k c i))]
    with x hzc hc hsmul hx
  rw [hzc hx,hc hx,hl]
  exact hsmul ((ball_subset_ball hba.le).trans ball_subset_closedBall hx)

def coefficientLinear : Input →ₗ[ℂ] ℂ where
  toFun := coefficient p a b k ha hb hai hba hk hfreq hν
  map_add' := coefficient_add p a b k ha hb hai hba hk hfreq hν
  map_smul' z c := coefficient_smul p a b k ha hb hai hba hk hfreq hν z c

theorem coefficient_of_expansion (c : Input) (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=
      ConicalEntireGauge.error p a k (FiniteAngularHerglotz.incident k c) i x)
    (q : ℂ)
    (he : ConicalGraphProjection.projected p
      (ConicalEntireGauge.system p a b k ha hai hba hk hfreq (FiniteAngularHerglotz.incident k c) J hJ heJ).graph
      =ᵐ[volume.restrict (Ioo (0 : ℝ) b)] fun r =>
        q*ConicalRadialParticular.power p.exponent r+ConicalRadialParticular.particular p.exponent
          (radialCorrection (ConicalEntireGauge.system p a b k ha hai hba hk hfreq (FiniteAngularHerglotz.incident k c) J hJ heJ))
          (tangentCorrection (ConicalEntireGauge.system p a b k ha hai hba hk hfreq (FiniteAngularHerglotz.incident k c) J hJ heJ)) r) :
    coefficient p a b k ha hb hai hba hk hfreq hν c=q := by
  let t := ConicalEntireGauge.system p a b k ha hai hba hk hfreq (FiniteAngularHerglotz.incident k c) J hJ heJ
  have htot : ∀ i : Fin 3, ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      totalCoordinate (system p a b k ha hai hba hk hfreq c) i x=1*totalCoordinate t i x := by
    intro i
    filter_upwards [ConicalEntireGauge.system_total_inner p a b k ha hai hba hk hfreq
      (FiniteAngularHerglotz.incident k c) J hJ heJ i,
      ConicalEntireGauge.system_total_inner p a b k ha hai hba hk hfreq
        (FiniteAngularHerglotz.incident k c) (extension p a b k hai hba c)
        (extension_continuous p a b k hai hba c) (extension_eq p a b k hai hba c) i] with x ht hs hx
    rw [one_mul]
    exact (hs hx).trans (ht hx).symm
  have h := ConicalNormalizedInputCoefficient.coefficient_scaled p b hb hν t
    (system p a b k ha hai hba hk hfreq c) 1 htot q _ he
    (ConicalIntrinsicCoefficient.coefficient_spec _ hb (hba.trans hai) hν)
  simpa only [one_mul] using h

/-- On a fixed finite set of actual angular modes, coefficient extraction is continuous. -/
def finiteCoefficient (s : Finset ModeIndex) : (s → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((coefficientLinear p a b k ha hb hai hba hk hfreq hν).comp
      ((Finsupp.linearCombination ℂ (fun m : s => Finsupp.single m.val (1 : ℂ))).comp
        (Finsupp.linearEquivFunOnFinite ℂ ℂ s).symm.toLinearMap))

end Device
theorem positive_frequency_nonzero (p : Data) (a b R : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (hba : b < a) (hR : 0 < R) (hRb : R < b) (hν : p.exponent < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (k : ℝ) (hk : 0 < k), k < δ →
      ∃ hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a,
        coefficientLinear p a b k ha (hR.trans hRb) hai hba hk.ne' hfreq hν≠0 := by
  obtain ⟨δ,hδ,hfix⟩ := ConicalFixedAngularInput.positive_frequency_fixed_input p a b R ha hai hba hR hRb hν
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  obtain ⟨hfreq,c,J,hJ,heJ,q,_,hq,he⟩ := hfix k hk hkd
  refine ⟨hfreq,?_⟩
  intro hz
  have h := coefficient_of_expansion p a b k ha (hR.trans hRb) hai hba hk.ne' hfreq hν c J
    (fun i => (hJ i).continuous) heJ q he
  have he0 : coefficient p a b k ha (hR.trans hRb) hai hba hk.ne' hfreq hν c=0 :=
    congrArg (fun L : Input →ₗ[ℂ] ℂ => L c) hz
  exact hq (h.symm.trans he0)

end OQ14.ConicalAngularCoefficient
#print axioms OQ14.ConicalAngularCoefficient.incident_add
#print axioms OQ14.ConicalAngularCoefficient.restricted_add
#print axioms OQ14.ConicalAngularCoefficient.extension_continuous
#print axioms OQ14.ConicalAngularCoefficient.extension_eq
#print axioms OQ14.ConicalAngularCoefficient.system_total_ae
#print axioms OQ14.ConicalAngularCoefficient.coefficient_add
#print axioms OQ14.ConicalAngularCoefficient.coefficient_smul
#print axioms OQ14.ConicalAngularCoefficient.coefficientLinear
#print axioms OQ14.ConicalAngularCoefficient.finiteCoefficient
#print axioms OQ14.ConicalAngularCoefficient.coefficient_of_expansion
#print axioms OQ14.ConicalAngularCoefficient.positive_frequency_nonzero
